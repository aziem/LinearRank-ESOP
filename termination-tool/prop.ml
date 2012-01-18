(** Functions for Propositions (i.e., Symbolic Heaps) *)

open Ident
open Sil
open Format

module E = Error

let cil_exp_compare (e1:Cil.exp) (e2:Cil.exp) = Pervasives.compare e1 e2

(** A proposition. The following invariants are mantained. [sub] is of
    the form id1=e1 ... idn=en where: the id's are distinct and do not
    occur in the e's nor in [pi] or [sigma]; the id's are in sorted
    order; the id's are not existentials; if idn=yn (for yn not
    existential) then idn<yn in the order on ident's. [pi] is sorted
    and normalized, and does not contain x=e. [sigma] is sorted and
    normalized. *)
type prop =
    {sid: int;
     sub: subst;
     pi:atom list;
     sigma: hpred list;
     visitedsid : int list;
		 wf : bool }

(** {2 Basic Functions for Propositions} *)

(** {1 Functions for Comparison} *)

(** Comparison between lists of equalities and disequalities. Lexicographical order. *)
let rec pi_compare pi1 pi2 =
  if pi1==pi2 then 0
  else match (pi1,pi2) with
    | ([],[]) -> 0
    | ([],_::_) -> -1
    | (_::_,[]) -> 1
    | (a1::pi1',a2::pi2') ->
	let n = atom_compare a1 a2
	in if n<>0 then n
	  else pi_compare pi1' pi2'

let pi_equal pi1 pi2 =
  pi_compare pi1 pi2 = 0

(** Comparsion between lists of heap predicates. Lexicographical order. *)
let rec sigma_compare sigma1 sigma2 =
  if sigma1==sigma2 then 0
  else match (sigma1,sigma2) with
    | ([],[]) -> 0
    | ([],_::_) -> -1
    | (_::_,[]) -> 1
    | (h1::sigma1',h2::sigma2') ->
	let n = hpred_compare h1 h2
	in if n<>0 then n
	  else sigma_compare sigma1' sigma2'

let sigma_equal sigma1 sigma2 =
  sigma_compare sigma1 sigma2 = 0

(** Comparison between propositions. Lexicographical order. *)
let prop_compare p1 p2 =
  let n = int_compare p1.sid p2.sid
  in if n<>0 then n
    else let n = sub_compare p1.sub p2.sub
      in if n<>0 then n
	else let n = pi_compare p1.pi p2.pi
	  in if n<>0 then n
	    else sigma_compare p1.sigma p2.sigma

let prop_equal p1 p2 = 
  (prop_compare p1 p2 = 0)

(** {1 Functions for Pretty Printing} *)

(** Print a sequence. *)
let rec pp_seq pp f = function
  | [] -> ()
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a,%a" pp x (pp_seq pp) l

(** Print a *-separated sequence. *)
let rec pp_star_seq pp f = function
  | [] -> ()
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a * %a" pp x (pp_star_seq pp) l

(** Pretty print a substitution. *)
let pp_sub f sub =
  let pi_sub = List.map (fun (id,e) -> Aeq(Var id,e)) (sub_to_list sub)
  in (pp_star_seq pp_atom) f pi_sub

(** Pretty print a pi. *)
let pp_pi =
  pp_star_seq pp_atom

(** Pretty print a sigma. *)
let pp_sigma =
  pp_star_seq pp_hpred

let pp_int f = function 
        | x -> fprintf f "%d" x

let pp_visited = 
        pp_seq pp_int 

(** Pretty print a proposition. *)
let pp_prop f prop =
  let pi_sub = List.map (fun (id,e) -> Aeq(Var id,e)) (sub_to_list prop.sub) in
  let pi = prop.pi @ pi_sub in
  let sigma = prop.sigma in
  let visited = prop.visitedsid 
  in fprintf f "[%d]%a%s%a Visited: %a" 
    prop.sid pp_pi pi 
    (match pi with [] -> "" | _ -> " * ")
    pp_sigma sigma 
    pp_visited visited

(** {1 Functions for computing free non-program variables} *)

let pi_fav_add fav pi =
  List.iter (atom_fav_add fav) pi

let pi_fav =
  fav_imperative_to_functional pi_fav_add

let sigma_fav_add fav sigma = 
  List.iter (hpred_fav_add fav) sigma

let sigma_fav =
  fav_imperative_to_functional sigma_fav_add

let prop_fav_add fav prop =
  sub_fav_add fav prop.sub;
  pi_fav_add fav prop.pi;
  sigma_fav_add fav prop.sigma

let prop_fav =
  fav_imperative_to_functional prop_fav_add

let rec hpred_fav_in_pvars_add fav = function
  | Hpointsto (Lvar _, sexp, _) -> strexp_fav_add fav sexp 
  | Hpointsto _  -> ()

let sigma_fav_in_pvars_add fav sigma =
  List.iter (hpred_fav_in_pvars_add fav) sigma

(** {2 Functions for Subsitition} *)

let pi_sub (subst:subst) pi =
  let f = atom_sub subst
  in List.map f pi

let sigma_sub subst sigma = 
  let f = hpred_sub subst
  in List.map f sigma


(** {2 Functions for normalization} *)

(** This function assumes that if (x,Var(y)) in sub, then ident_compare x y = 1 *)
let sub_normalize sub = 
    let sub' = sub_filter (fun i -> not (ident_is_primed i)) sub
    in if sub_equal sub sub' then sub else sub'

let rec sym_eval e = match e with
  | Var _ | Const_int _ -> 
     e 
  | Cast (_, e1) -> 
     sym_eval e1
  | UnOp (op, e1) ->
     let e1' = sym_eval e1 
     in begin 
        match op, e1' with
          | Cil.Neg, (UnOp(Cil.Neg,e2')) -> e2'  
          | Cil.Neg, Const_int n -> Const_int (-n)
          | Cil.BNot, (UnOp(Cil.BNot,e2')) -> e2'  
          | Cil.LNot, (UnOp(Cil.LNot,e2')) -> e2'  
          | _ -> UnOp(op, e1')
      end
  | BinOp (op, e1, e2) ->
     let e1' = sym_eval e1 in
     let e2' = sym_eval e2 
     in begin 
        match op, e1', e2' with
          | Cil.PlusA, Const_int 0, _ -> e2'
          | Cil.PlusA, _, Const_int 0 -> e1'
          | Cil.PlusA, Const_int n, Const_int m -> Const_int (n+m)
          | Cil.MinusA, Const_int 0, _ -> sym_eval (UnOp(Cil.Neg, e2'))
          | Cil.MinusA, _, Const_int 0 -> e1'
          | Cil.MinusA, Const_int n, Const_int m -> Const_int (n-m)
          | Cil.Mult, Const_int 1, _ -> e2'
          | Cil.Mult, _, Const_int 1 -> e1'
          | Cil.Mult, Const_int -1, _ -> sym_eval (UnOp(Cil.Neg, e2'))
          | Cil.Mult, _, Const_int -1 -> sym_eval (UnOp(Cil.Neg, e1'))
          | Cil.Mult, Const_int 0, _ -> Const_int 0
          | Cil.Mult, _, Const_int 0 -> Const_int 0
          | Cil.Mult, Const_int n, Const_int m -> Const_int (n*m)
          | _ -> BinOp(op, e1',e2')
      end
  | Lvar _ | Fvar _  -> 
     e
  | Lfield (e1,fld) ->
     let e1' = sym_eval e1 
     in Lfield (e1', fld)
  | Lindex (e1,e2) ->
     let e1' = sym_eval e1 in
     let e2' = sym_eval e2 
     in Lindex (e1',e2')

let rec exp_normalize sub exp = 
  let exp' = exp_sub sub exp 
  in sym_eval exp'

let atom_normalize sub a = match a with
  | Aeq (e1,e2) ->
      let e1' = exp_normalize sub e1 in
      let e2' = exp_normalize sub e2 
      in if exp_compare e1' e2' <> 1 then Aeq (e1',e2')
        else Aeq(e2',e1')
  | Aneq (e1,e2) ->
      let e1' = exp_normalize sub e1 in
      let e2' = exp_normalize sub e2 
      in if exp_compare e1' e2' <> 1 then Aneq (e1',e2') 
        else Aneq(e2',e1')
  | Aless (e1,e2) -> 
      let e1' = exp_normalize sub e1 in
      let e2' = exp_normalize sub e2 
      in Aless(e1',e2')
  | Aleq (e1,e2) ->
      let e1' = exp_normalize sub e1 in
      let e2' = exp_normalize sub e2 
      in Aleq(e1',e2')

let rec remove_duplicates_from_sorted special_equal = function
  | [] -> []
  | [x] -> [x]
  | x::y::l -> 
      if (special_equal x y) 
      then remove_duplicates_from_sorted special_equal (y::l)
      else x::(remove_duplicates_from_sorted special_equal (y::l))

let rec strexp_normalize sub = function
  | Eexp e -> Eexp (exp_normalize sub e)
  | Estruct fld_cnts ->
      let fld_cnts' = List.map 
        (fun (fld,cnt) -> (fld,strexp_normalize sub cnt)) 
        fld_cnts in
      let fld_cnts'' = List.sort fld_strexp_compare fld_cnts' 
      in Estruct fld_cnts'' 
  | Earray (size, idx_cnts) ->
      let idx_cnts' = List.map 
        (fun (idx,cnt) -> (exp_normalize sub idx,strexp_normalize sub cnt)) 
        idx_cnts in
      let idx_cnts'' = List.sort exp_strexp_compare idx_cnts'
      in Earray (size, idx_cnts'')

let rec hpred_normalize sub = function
  | Hpointsto (root, cnt, t) -> 
      let normalized_root = exp_normalize sub root in
      let normalized_cnt = strexp_normalize sub cnt 
      in Hpointsto (normalized_root, normalized_cnt, t)

let pi_normalize sub pi =
  let filter_useful_atom = function
    | Aeq(Const_int n, Const_int m) -> n<>m
    | Aneq(Const_int n, Const_int m) -> n=m
    | _ -> true in
  let pi' = List.filter filter_useful_atom (pi_sub sub pi)
  in if pi_equal pi pi' then pi
    else remove_duplicates_from_sorted atom_equal (List.stable_sort atom_compare pi')

let sigma_normalize sub sigma =
  let sigma' =
    List.stable_sort hpred_compare (List.map (hpred_normalize sub) sigma)
  in if sigma_equal sigma sigma' then sigma else sigma'

let exp_normalize_prop prop exp = 
  exp_normalize prop.sub exp

let atom_normalize_prop prop atom =
  atom_normalize prop.sub atom

let hpred_normalize_prop prop hpred =
  hpred_normalize prop.sub hpred

let sigma_normalize_prop prop sigma =
  sigma_normalize prop.sub sigma

(** {2 Query about Proposition} *)

(** Check if the proposition is pure *)
let prop_is_pure p = match p.sigma with
  | [] -> true
  | _ -> false

(** {2 Functions for changing and generating propositions} *)

(** Construct a pointsto. *)
let mk_ptsto lexp sexp typ =
  let nsexp = strexp_normalize sub_empty sexp 
  in Hpointsto(lexp,nsexp,typ)

let unstructured_type = function
  | Tstruct _ | Tarray _ -> false
  | _ -> true

(** Construct a points-to predicate for an expression using either the
    provided expression [name] as base for fresh identifiers. *)
let mk_ptsto_exp name (exp,typ,expo) : hpred =  
  let strexp =
    match expo with
      | Some e -> Eexp e
      | None ->
	  (match typ with
	    | Tint | Tvoid  | Tfun | Tptr _ -> 
		let rv' = create_fresh_primed_ident name
		in Eexp (Var rv')
	    | Tstruct ftl ->
		Estruct []
	    | Tarray (_,n) -> Earray (n,[])
	    | Tvar _ -> assert false (* Tvar should always appear inside Tptr *))
  in mk_ptsto exp strexp typ


(** Construct a points-to predicate for a single program variable. *)
let mk_ptsto_lvar ((pvar:pvar),typ,expo) : hpred =
  mk_ptsto_exp (pvar_get_name pvar) (Lvar pvar,typ,expo)


(** Proposition [true /\ emp] at sid. *)
let prop_emp (sid:int) : prop  = {sid=sid; sub=sub_empty;pi=[];sigma=[];visitedsid = [];wf=true}

(** Conjoin a heap predicate by separating conjunction. *)
let prop_hpred_star (p : prop) (h : hpred) : prop = 
  let sigma' = sigma_normalize p.sub (h::p.sigma)
  in {p with sigma=sigma'}

let prop_sigma_star (p : prop) (sigma : hpred list) : prop =
  let sigma' = sigma_normalize p.sub (sigma@p.sigma)
  in {p with sigma=sigma'}


let prop_addvisited p i   = 
    let v = i::(p.visitedsid) in 
    {p with visitedsid = v}


let prop_set_wf p b = 
	{p with wf=b}

let prop_is_wf p = p.wf

(** Conjoin a pure atomic predicate by normal conjunction. *)
let rec prop_atom_and (p : prop) (a : atom) : prop =
  let a' = atom_normalize p.sub a 
  in match a' with
    | Aeq (Var i, e) when ident_in_exp i e -> 
         E.log "@..... [prop_atom_and] DROPPING (nested) %a ....@." pp_atom a'; 
         p
    | Aeq (Var i, e) ->
  	let sub_list = [(i, e)] in
	let mysub = sub_of_list sub_list in
	let sub' = sub_join mysub (sub_range_map (exp_sub mysub) p.sub) in
	let (sub'', pi'', sigma'') = 
          (sub_normalize sub', pi_normalize sub' p.pi, sigma_normalize sub' p.sigma) 
        in
           E.log "@..... [prop_atom_and] ADDING (sub) %a ....@." pp_atom a'; 
           {p with sub=sub''; pi=pi''; sigma=sigma''}
    | Aeq (e1, e2) when exp_compare e1 e2 = 0 -> 
           E.log "@..... [prop_atom_and] DROPPING (eq) %a ....@." pp_atom a'; 
           p
    | _ ->
	let pi' = pi_normalize p.sub (a'::p.pi)
        in
           E.log "@..... [prop_atom_and] ADDING (pi) %a ....@." pp_atom a'; 
	   {p with pi=pi'}
      
(** Conjoin [exp1]=[exp2] with a symbolic heap [prop]. *)
let conjoin_eq exp1 exp2 prop =
  prop_atom_and prop (Aeq (exp1,exp2))

(** Conjoin [exp1!=exp2] with a symbolic heap [prop]. *)
let conjoin_neq exp1 exp2 prop =
  prop_atom_and prop (Aneq (exp1,exp2))

(** Conjoin [exp1<exp2] with a symbolic heap [prop]. *)
let conjoin_less exp1 exp2 prop =
  prop_atom_and prop (Aless (exp1,exp2))

(** Conjoin [exp1<=exp2] with a symbolic heap [prop]. *)
let conjoin_leq exp1 exp2 prop =
  prop_atom_and prop (Aleq (exp1,exp2))

(** Return the statement id of [prop] *)
let prop_get_sid (p:prop) = p.sid

(** Return the equalities in the proposition *)
let prop_get_equalities (p:prop) =
  let eq1 = List.map (fun (i,e) -> (Var i,e)) (sub_to_list p.sub) in
  let pieq = List.filter (function Aeq _ -> true | _ -> false) p.pi in
  let eq2 = List.map (function Aeq(e1,e2) -> e1,e2 | _ -> assert false) pieq
  in eq1 @ eq2

(** Return the sub part of [prop]. *)
let prop_get_sub (p:prop) : subst = p.sub

(** Return the pi part of [prop]. *)
let prop_get_pi (p:prop) : atom list = p.pi

(** Return the pure part of [prop]. *)
let prop_get_pure (p:prop) : atom list =
  List.map (fun (id1,e2) -> Aeq (Var id1,e2)) (sub_to_list p.sub) @ p.pi


let prop_get_visited (p:prop) : int list = 
        p.visitedsid

let prop_set_visited (p:prop) (v:int list) : prop = 
        {p with visitedsid = v}

(** Replace the pi part of [prop]. *)
let prop_replace_pi pi p = 
  let npi = pi_normalize p.sub pi 
  in {p with pi = npi}

(** Return the spatial part *)
let prop_get_sigma (p:prop) : hpred list = p.sigma

(** Replace the sigma part of [prop] *)
let prop_replace_sigma sigma p =
  let nsigma = sigma_normalize p.sub sigma
  in {p with sigma = nsigma}

let prop_get_allocated_stack_vars p =
  let sigma = prop_get_sigma p in
  let rec f pvars_acc = function 
    | [] -> 
	List.rev pvars_acc
    | Hpointsto (Lvar pvar, _, _) :: sigma_rest -> 
	f (pvar::pvars_acc) sigma_rest  
    | Hpointsto _ :: sigma_rest ->
	f pvars_acc sigma_rest in
  let pvars = f [] sigma
  in List.sort pvar_compare pvars

(** Initialize proposition for execution given formal and global parameters. *)
let prop_init_formals_locals formals locals prop : prop =
  let normalize_param (id,typ,expo) = match expo with
    | None -> (id,typ,expo)
    | Some e -> (id,typ,Some (exp_normalize_prop prop e)) in
  let sigma_formals = List.map (fun param -> mk_ptsto_lvar (normalize_param param)) formals in
  let sigma_locals = List.map (fun param -> mk_ptsto_lvar (normalize_param param)) locals in
  let sigma = sigma_formals @ sigma_locals 
  in
    prop_sigma_star prop sigma

(** {2 Functions for renaming primed variables by "canonical names"} *)      

let id_dummy = 
  let name_dummy = string_to_name "dummy" 
  in create_fresh_normal_ident name_dummy

(** This function works correctly only when 
    ident_compare compares first kind and
    name, and next stamps. So, if we change ident_compare,
    the function has to be changed as well. *)
let compute_renaming (eids:fav) : subst = 
  let sorted_eids = fav_to_list eids in
  let f ((kind,name,prev_idx),ren_subst) id =
    if (prev_idx = -1) || 
      (not (name_equal name (ident_name id))) || 
      (not (kind_equal kind (ident_kind id))) then 
      let new_name = ident_name id in
      let new_kind = ident_kind id in
      let new_idx = 0 in
      let new_id = ident_set_stamp id 0
      in if new_idx = ident_get_stamp id then ((new_kind,new_name,new_idx),ren_subst)
        else ((new_kind,new_name,new_idx), (id,new_id)::ren_subst)
    else 
      let new_idx = prev_idx + 1 in
      let new_id = ident_set_stamp id new_idx 
      in if new_idx = ident_get_stamp id then ((kind,name,new_idx),ren_subst) 
        else ((kind,name,new_idx), (id,new_id)::ren_subst) in
  let (_,ren) =  List.fold_left f ((ident_kind id_dummy,ident_name id_dummy,-1),[]) sorted_eids in
  let ren' = List.map (fun (id1,id2) -> (id1, Var id2)) ren 
  in sub_of_list ren'
  
(** Canonicalize the names of primed vars. *)
let prop_rename_primed_vars p = 
  let bound_vars = 
    let filter id = ident_is_primed id in 
    let fvars_in_p = prop_fav p 
    in fav_filter_ident fvars_in_p filter;
      fvars_in_p in
  let ren_sub = compute_renaming bound_vars in
  let sub' = sub_range_map (exp_sub ren_sub) p.sub in 
  let pi' = pi_sub ren_sub p.pi in
  let sigma' = sigma_sub ren_sub p.sigma in
  let sub_for_normalize = sub_empty in 
    (* It is fine to use the empty substituion during normalization 
       because the renaming maintains that a substitution is normalized *)
  let npi' = pi_normalize sub_for_normalize pi' in
  let nsigma' = sigma_normalize sub_for_normalize sigma' 
  in { p with sub=sub';pi=npi';sigma=nsigma' }


let prop_make_id_primed id prop =
  let pid = create_fresh_primed_ident (ident_name id) in
  let sub_id = sub_of_list [(id, Var pid)] in
  let sub_new =
    let f (id,e) = 
      atom_normalize sub_empty (Aeq(exp_sub sub_id (Var id), exp_sub sub_id e)) in 
    let eqs = List.map f (sub_to_list prop.sub) in
    let g sub_acc = function 
      | Aeq (Var id1, e1) when ident_in_exp id1 e1 -> 
	  assert false
      | Aeq (Var id1, e1) ->
	  let sub = sub_of_list [(id1,e1)] 
          in if not (ident_equal pid id1) then (id1,e1) :: sub_acc 
            else (id1,e1) :: List.map (fun (e_id,e) -> (e_id, exp_sub sub e)) sub_acc 
      | _ -> assert false 
    in sub_of_list (List.fold_left g [] eqs) in
  let nsub_new = sub_normalize sub_new 
  in 
    { prop with
      sub=nsub_new;
      pi=pi_sub sub_new prop.pi;
      sigma=sigma_sub sub_new prop.sigma}


(** {2 Functionss for changing and generating propositions} *)

let mem_idlist i l =
  List.exists (fun id -> ident_equal i id) l

(** Apply renaming substitution to a proposition. *)
let prop_ren_sub (ren_sub:subst) (prop:prop) =
  let sub' = sub_range_map (exp_sub ren_sub) prop.sub in
  let (sub_change,sub_keep) =
    let filter = function
      | Var i -> ident_is_primed i (** need to change x=y if y becomes _y *)
      | _ -> false
    in sub_range_partition filter sub' in
  let prop' = 
    let pi' = pi_sub ren_sub prop.pi in
    let npi' = pi_normalize sub_keep pi' in
    let sigma' = sigma_sub ren_sub prop.sigma in
    let nsigma' = sigma_normalize sub_keep sigma' 
    in { prop with sub=sub_keep;pi=npi';sigma=nsigma' } in
  let res_prop =
    let add (i1,e) p = match e with
      | Var i2 -> prop_atom_and p (Aeq (Var i1, e))
      | _ -> assert false
    in List.fold_right add (sub_to_list sub_change) prop'
  in if prop_compare prop res_prop = 0 then prop else res_prop

(** Existentially quantify the [fav] in [prop]. 
    [fav] should not contain any primed variables. *)
let exist_quantify fav prop =
  let ids = fav_to_list fav in
  let _ = if List.exists ident_is_primed ids then assert false else ()  (* sanity check *) in
  let ren_sub = sub_of_list (List.map (fun i -> (i, Var (create_fresh_primed_ident (ident_name i)))) ids) in
  let prop' =
    let sub = sub_filter (fun i -> not (mem_idlist i ids)) prop.sub (** throw away x=E if x becomes _x *)
    in if sub_equal sub prop.sub then prop
      else {prop with sub=sub}
  in prop_ren_sub ren_sub prop'

(** Apply renaming substitution to a proposition. *)
let prop_sub (sub_to_apply:subst) (prop:prop) =
  let new_sub_list =
    let sub_list = sub_to_list prop.sub in
    let f (id,e) =
      let e_id' = exp_sub sub_to_apply (Var id) in
      let e' = exp_sub sub_to_apply e 
      in (e_id', e') 
    in List.map f sub_list in
  let new_pi =
    let pi' = pi_sub sub_to_apply prop.pi 
    in pi_normalize sub_empty pi' in
  let new_sigma = 
    let sigma' = sigma_sub sub_to_apply prop.sigma
    in sigma_normalize sub_empty sigma' in
  let new_prop =
    let prop' = { prop with sub=sub_empty; pi=new_pi; sigma=new_sigma } in
    let add p (e1,e2) = conjoin_eq e1 e2 p
    in List.fold_left add prop' new_sub_list
  in 
    if prop_equal prop new_prop then prop else new_prop

(**  Composition of Propositions}*)
(** Read two propositions as relations and compose them.  Assume that
    the same set of program variables are allocated in the given
    propositions. Assume that no normal variables appear in p1 and
    p2. *)
let prop_compose p1 p2 = 
  let _    =  (* STEP1 : sanity check *) 
    let pvars1 = prop_get_allocated_stack_vars p1 in
    let pvars2 = prop_get_allocated_stack_vars p2 
    in if pvar_list_equal pvars1 pvars2 then () else assert false in
  let p2'  = (* STEP2 : replace all primed variables in p2 by fresh primed vars *)
    let fav = prop_fav p2 in
    let ids = List.filter ident_is_primed (fav_to_list fav) in
    let sub = sub_of_list (List.map (fun i -> (i, Var (create_fresh_primed_ident (ident_name i)))) ids)
    in prop_sub sub p2 in
  let sub  = (* STEP3 : compute a substitution from p1 *)
    let sigma1 = prop_get_sigma p1 in
    let rec f sub_acc = function 
      | [] -> sub_of_list (List.rev sub_acc)
      | Hpointsto(Lvar pvar, Eexp e, _)::sigma_rest ->
	  let x = pvar_get_name pvar in
	  let x0 = get_default_footprint_ident x in
	  let sub_acc' = (x0,e)::sub_acc
	  in f sub_acc' sigma_rest
      | Hpointsto(Lvar pvar, _, _)::sigma_rest -> assert false
      | Hpointsto _::sigma_rest -> f sub_acc sigma_rest
    in f [] sigma1 in
  let p2'' = (* STEP4 : replace initial variables (AKA footprint variables) x0 *)
    prop_sub sub p2' in
  let new_p = (* STEP5 : combine two heaps *)
    let new_sigma = sigma_normalize p1.sub p2''.sigma in
    let p = {p1 with sigma = new_sigma} in
    let atoms_from_sub2 = List.map (fun (id,e) -> Aeq(Var id, e)) (sub_to_list p2''.sub) in
    let atoms_from_p2 = p2''.pi@atoms_from_sub2
    in List.fold_left prop_atom_and p atoms_from_p2 
  in new_p



(** {2 Prop iterators} *)
(* Hongseok's comment: Many of prop_iter ignores the pit_old part of
 * sigma. For instance, prop_iter_map applies a given function f only to
 * the pit_curr and pit_new. I am slightly worried that this might cause
 * some problems. *)

(** Iterator state over sigma. *)
type 'a prop_iter =
     {pit_wf : bool;
		 pit_visitedsid : int list;
     pit_sid : int; (** statement id *)
     pit_sub : subst; (** substitution for equalities *)
     pit_pi : atom list;    (** pure part *)
     pit_old : hpred list; (** sigma already visited *)
     pit_curr : hpred;      (** current element *)
     pit_state : 'a option; (** state of current element *)
     pit_new : hpred list; (** sigma not yet visited *)
    }

let prop_iter_create prop =
  match prop.sigma with
    | hpred::sigma' -> Some
         {pit_wf = prop.wf;
					pit_visitedsid = prop.visitedsid;
         pit_sid = prop.sid;
         pit_sub = prop.sub;
	 pit_pi = prop.pi;
	 pit_old = [];
	 pit_curr = hpred;
	 pit_state = None;
	 pit_new = sigma'}
    | _ -> None

(** Return the prop associated to the iterator. *)
let prop_iter_to_prop iter =
  let sigma = List.rev_append iter.pit_old (iter.pit_curr::iter.pit_new) in
  let normalized_sigma = sigma_normalize iter.pit_sub sigma 
  in {
      sid = iter.pit_sid; 
      sub = iter.pit_sub; 
      pi = iter.pit_pi; 
      sigma = normalized_sigma;
      visitedsid = iter.pit_visitedsid;
			wf=iter.pit_wf}

(** Remove the current element of the iterator, and return the prop
    associated to the resulting iterator *)
let prop_iter_remove_curr_then_to_prop iter =
  let sigma = List.rev_append iter.pit_old iter.pit_new in
  let normalized_sigma = sigma_normalize iter.pit_sub sigma 
  in {sid = iter.pit_sid;
      sub = iter.pit_sub;
      pi = iter.pit_pi;
      sigma = normalized_sigma;
      visitedsid = iter.pit_visitedsid;
		  wf = iter.pit_wf}

(** Return the current hpred and state. *)
let prop_iter_current iter =
  (iter.pit_curr, iter.pit_state)

(** Update the current element of the iterator. *)
let prop_iter_update_current iter hpred =
 {iter with pit_curr = hpred; pit_state = None}

(** Update the current element of the iterator by a nonempty list of
    elements. *)
let prop_iter_update_current_by_list iter = function
  | [] -> assert false (* the list should be nonempty *)
  | hpred::hpred_list -> 
      let pit_new' = hpred_list@iter.pit_new 
      in {iter with pit_curr=hpred; pit_state=None; pit_new=pit_new'}

let prop_iter_next iter =
  match iter.pit_new with
    | [] -> None
    | hpred'::new' -> Some
	{iter with
	  pit_old = iter.pit_curr::iter.pit_old;
	  pit_curr = hpred';
	  pit_state = None;
	  pit_new = new'}

let prop_iter_remove_curr_then_next iter =
  match iter.pit_new with
    | [] -> None
    | hpred'::new' -> Some
	{iter with
	  pit_old = iter.pit_old;
	  pit_curr = hpred';
	  pit_state = None;
	  pit_new = new'}

let prop_iter_prev_then_insert iter hpred =
  {iter with 
     pit_new = iter.pit_curr::iter.pit_new;
     pit_curr = hpred }


(** Scan sigma to find an [hpred] satisfying the filter function. *)
let rec prop_iter_find iter filter =
  match filter iter.pit_curr with
    | Some st -> Some {iter with pit_state=Some st}
    | None ->
	(match prop_iter_next iter with
	  | None -> None
	  | Some iter' -> prop_iter_find iter' filter)

(** Return the root of [lexp]. *)
let rec root_of_lexp lexp = match lexp with
    | Var _ -> lexp
    | Const_int _ -> lexp
    | Cast (t,e) -> root_of_lexp e
    | UnOp _ | BinOp _ -> lexp
    | Lvar _ -> lexp
    | Fvar _ -> lexp
    | Lfield(e,_) -> root_of_lexp e
    | Lindex(e,_) -> root_of_lexp e


(** Set the state of the iterator *)
let prop_iter_set_state iter state =
  {iter with pit_state = Some state}

let prop_iter_make_id_primed id iter =
  let pid = create_fresh_primed_ident (ident_name id) in
  let sub_id = sub_of_list [(id, Var pid)] in
  let sub_new =
    let f (id,e) = 
      atom_normalize sub_empty (Aeq(exp_sub sub_id (Var id), exp_sub sub_id e)) in 
    let eqs = List.map f (sub_to_list iter.pit_sub) in
    let g sub_acc = function 
      | Aeq (Var id1, e1) when ident_in_exp id1 e1 -> assert false
      | Aeq (Var id1, e1) ->
	  let sub = sub_of_list [(id1,e1)] 
          in if not (ident_equal pid id1) then (id1,e1) :: sub_acc 
            else (id1,e1) :: List.map (fun (e_id,e) -> (e_id, exp_sub sub e)) sub_acc 
      | _ -> assert false 
    in sub_of_list (List.fold_left g [] eqs) in
  let nsub_new = sub_normalize sub_new 
  in {iter with
    pit_sub = nsub_new;
    pit_pi = pi_sub sub_new iter.pit_pi;
    pit_old = sigma_sub sub_new iter.pit_old;
    pit_curr = hpred_sub sub_new iter.pit_curr;
    pit_new = sigma_sub sub_new iter.pit_new}

(** Free vars of the iterator except the current hpred (and footprint). *)
let prop_iter_noncurr_fav_add fav iter =
  sub_fav_add fav iter.pit_sub;
  pi_fav_add fav iter.pit_pi;
  sigma_fav_add fav iter.pit_old;
  sigma_fav_add fav iter.pit_new

let prop_iter_noncurr_fav iter =
  fav_imperative_to_functional prop_iter_noncurr_fav_add iter

let unSome = function
  | Some x -> x
  | _ -> assert false

let rec strexp_gc_fields (fav:fav) se = match se with
  | Eexp e -> (match e with
      | Var id ->
	  if fav_mem fav id 
	  then Some se
	  else None
      | _ -> Some se)
  | Estruct fsel ->
      let fselo = List.map (fun (f,se) -> (f,strexp_gc_fields fav se)) fsel in
      let fsel' =
	let fselo' = List.filter (function | (_,Some _) -> true | _ -> false) fselo
	in List.map (function (f,seo) -> (f,unSome seo)) fselo'
      in if fld_strexp_list_compare fsel fsel' = 0 then Some se
	else Some (Estruct fsel')
  | Earray _ -> Some se

let hpred_gc_fields (fav:fav) hpred = match hpred with
  | Hpointsto (e,se,t) ->
      (match strexp_gc_fields fav se with
	| None -> hpred
	| Some se' ->
	    if strexp_compare se se' = 0 then hpred
	    else Hpointsto (e,se',t))
	

let rec prop_iter_map f iter =
  let hpred_curr = f iter in
  let iter' = {iter with pit_curr = hpred_curr} 
  in match prop_iter_next iter' with
    | None -> iter'
    | Some iter'' -> prop_iter_map f iter''

(** Collect garbage fields. *)
let prop_iter_gc_fields iter =
  let f iter' =
    let fav = prop_iter_noncurr_fav iter'
    in hpred_gc_fields fav iter'.pit_curr
  in prop_iter_map f iter
