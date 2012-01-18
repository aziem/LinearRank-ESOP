(** Symbolic Execution *)

open Ident
open Sil
open Prop
open Propset
open Prover

module E = Error

(** Raised when a program possibly dereferences a dangling pointer. *)
  
exception MEMORY_ERROR

let rec idlist_assoc id = function
  | [] -> raise Not_found
  | (i,x)::l -> if ident_equal i id then x else idlist_assoc id l

let rec fldlist_assoc fld = function
  | [] -> raise Not_found
  | (fld',x)::l -> if fld_equal fld fld' then x else fldlist_assoc fld l

let rec explist_assoc e = function
  | [] -> raise Not_found
  | (e',x)::l -> if exp_equal e e' then x else explist_assoc e l

let rec unroll_type typ off = match (typ,off) with
  | (Tvar tname,_) -> 
      begin
	match tenv_lookup tname with
	  | Some typ' -> unroll_type typ' off
	  | None -> assert false
      end 
  | (Tstruct ftl, Off_fld fld) -> 
      (try fldlist_assoc fld ftl 
	with Not_found -> 
	  begin
            E.err "@.#### ERROR: Invalid Field Access (Fld : %a, Type : %a) ####@.@." pp_name fld pp_typ typ; 
            (* assert false *) raise MEMORY_ERROR
	  end)
  | (Tarray (typ',_), Off_index _) ->
      typ'
  | _ -> assert false


let rec unroll_strexp strexp off = match (strexp,off) with
  | (Estruct fsel, Off_fld fld) ->
      (try Some (fldlist_assoc fld fsel)
	with Not_found -> None)
  | (Earray (_,isl),Off_index e) ->
      (try Some (explist_assoc e isl)
	with Not_found -> None)
  | _ -> assert false


let list_split equal x xys = 
  let (xy,xys') = List.partition (fun (x',_) -> equal x x') xys 
  in match xy with
    | [] -> (xys', None)
    | [(x',y')] -> (xys', Some y')
    | _ -> assert false

let rec construct_strexp exp offlist typ = 
  match offlist with
    | [] -> Eexp exp
    | off::offlist'-> 
	let typ' = unroll_type typ off in  
	let strexp = construct_strexp exp offlist' typ' 
        in match (off,typ) with
	  | (Off_fld fld, _) -> Estruct [(fld,strexp)]
	  | (Off_index n, Tarray(_,size)) -> Earray (size, [(n,strexp)])
	  | _ -> assert false

(** apply function [f] to the expression at position [offlist] in [strexp]
    if not found, expand [strexp] and apply [f] to [None] *)
let rec apply_offlist strexp typ offlist (f: exp option -> exp) =
  match (offlist,strexp) with
    | ([],Eexp e) -> let e' = f (Some e) in  (e', Eexp e')
    | ((Off_fld fld)::offlist',Estruct fsel) ->
	let typ' = unroll_type typ (Off_fld fld) in
        let (fsel', strexpo) = list_split name_equal fld fsel  
	in begin match strexpo with
	  | Some strexp' ->
	      let (e',strexp'') = apply_offlist strexp' typ' offlist' f
	      in (e', Estruct ((fld,strexp'')::fsel'))
		(* Hongseok's comment: The list above is no longer
		 * sorted above.  The invariant has to be
		 * re-restablished somewhere else *)
	  | None ->
	      let e' = f None in
              let strexp'' = construct_strexp e' offlist' typ' 
	      in (e', Estruct ((fld,strexp'')::fsel'))
		(* Hongseok's comment: The list above is no longer
		 * sorted above.  The invariant has to be
		 * re-restablished somewhere else *)
	end
    | ((Off_index n)::offlist',Earray (size,isl)) ->
	let typ' = unroll_type typ (Off_index n) in
	let (isl', strexpo) = list_split exp_equal n isl 
	in begin match strexpo with
	  | Some strexp' ->
	      let (e',strexp'') = apply_offlist strexp' typ' offlist' f
	      in (e', Earray (size,(n,strexp'')::isl'))
		(* Hongseok's comment: The list above is no
		 * longer sorted above.  The invariant has to be
		 * re-restablished somewhere else *)
	  | None ->
	      let e' = f None in
	      let strexp'' = construct_strexp e' offlist' typ'
	      in (e', Earray (size, (n,strexp'')::isl'))
		(* Hongseok's comment: The list above is no longer
		 * sorted above.  The invariant has to be
		 * re-restablished somewhere else *)
	end
    | _ -> assert false

(** [ptsto_lookup (lexp,strexp,typ) offlist id] given
    [lexp|->strexp:typ] returns the expression at position
    [offlist] in [strexp], together with [strexp], if the
    location [offlist] exists in [strexp]. If the location
    does not exist, it constructs [strexp'] containing
    [id] at [offlist], and returns ([ident],[strexp']).*)
let ptsto_lookup (lexp,strexp,typ) offlist id =
  let f = function
    | Some exp -> exp
    | None -> Var id
  in apply_offlist strexp typ offlist f

(** [ptsto_update (lexp,strexp,typ) offlist exp] given
    [lexp|->strexp:typ] returns an updated [strexp] obtained by
    replacing the expression at [offlist] with [exp]. *)
let ptsto_update (lexp,strexp,typ) offlist exp =
  let f _ = exp
  in snd (apply_offlist strexp typ offlist f)

(* Exposes lexp|->- from iter. In case that it is not possible to
 * expose lexp|->-, this function prints an error message and
 * faults. There are two things to note. First, typ is the type of the
 * root of lexp. Second, prop should mean the same as iter.  *)
let rec iter_rearrange lexp typ prop iter : (offset list) prop_iter list = 
  let filter = function
    | Hpointsto (base,_,_) -> 
        is_root prop base lexp 
  in match (prop_iter_find iter filter) with
    | None -> raise MEMORY_ERROR
    | Some iter -> [iter]


(** [rearrange lexp typ prop] rearranges [prop] such that [lexp|->...] is
    exposed. [exp|->strexp:typ] is the exposed points-to predicate,
    and [offset list] is the path that leads to the exposed position
    inside [strexp]. *)
let rearrange lexp typ prop =
  let lexp = exp_normalize_prop prop lexp 
  in 
    match prop_iter_create prop with
      | None -> raise MEMORY_ERROR
      | Some iter -> iter_rearrange lexp typ prop iter 

let execute_letderef id rhs_exp iter =
  let iter_ren = prop_iter_make_id_primed id iter in
  let (lexp,strexp,typ,offlist) = match prop_iter_current iter_ren with
    | (Hpointsto(lexp,strexp,typ), Some offlist) -> (lexp,strexp,typ,offlist)
    | (Hpointsto _, None) -> assert false in
  let (contents,new_strexp) = ptsto_lookup (lexp,strexp,typ) offlist id in
  let new_ptsto = mk_ptsto lexp new_strexp typ in
  let iter_res = prop_iter_update_current iter_ren new_ptsto in
  let prop_res = prop_iter_to_prop iter_res 
  in conjoin_eq (Var(id)) contents prop_res

let execute_set lhs_exp rhs_exp iter = 
  let (lexp,strexp,typ,offlist) = match prop_iter_current iter with
    | (Hpointsto(lexp,strexp,typ),Some offlist) -> (lexp,strexp,typ,offlist)
    | _ -> assert false in
  let new_strexp = ptsto_update (lexp,strexp,typ) offlist rhs_exp in
  let new_ptsto = mk_ptsto lexp new_strexp typ in
  let iter' = prop_iter_update_current iter new_ptsto
  in prop_iter_to_prop iter'

(** Execute [instr] with a symbolic heap [prop].*)
let _sym_exec instr (prop:prop) =
  match instr with
    | Letderef (id,rhs_exp,typ,loc) -> begin 
	try
          let iter_list = rearrange rhs_exp typ prop 
          in List.map (execute_letderef id rhs_exp) iter_list
	with MEMORY_ERROR ->
	  [prop_make_id_primed id prop]
      end
    | Set (lhs_exp,typ,rhs_exp,loc) -> begin 
	(* Hongseok: Assume that if the rearrangement fails, the cell is
	 * in the heap. Possible Source of Unsoundness. *)
	try
          let iter_list = rearrange lhs_exp typ prop 
	  in List.map (execute_set lhs_exp rhs_exp) iter_list
	with MEMORY_ERROR -> [prop]
      end
    | Call (Some(Lvar pvar as e,t1,_),_,_,_) -> 
        begin 
          try
            let iter_list = rearrange e t1 prop in
            let pvar_name = pvar_get_name pvar in
            let var' = create_fresh_primed_ident pvar_name 
	    in List.map (execute_set e (Var var')) iter_list
	  with MEMORY_ERROR -> [prop]
        end
    | Call (_, e, _,loc) -> [prop] 
	(* currently, we regard all function calls as skip *)
	
let sym_exec instr (prop:prop) =
  proplist2propset (_sym_exec instr prop)

let rec prune_polarity positive (condition : exp) (pset : propset) = match condition with
  | Var _ | Lvar _ ->
      prune_polarity positive (BinOp ((if positive then Cil.Ne else Cil.Eq), condition, Const_int 0)) pset
  | Const_int 0 ->
      if positive then propset_empty else pset
  | Const_int _ | Fvar _ ->
      if positive then pset else propset_empty
  | Cast (_,condition') ->
      prune_polarity positive condition' pset
  | UnOp (Cil.LNot,condition') ->
      prune_polarity (not positive) condition' pset
  | UnOp _ ->
      assert false
  | BinOp (Cil.Eq, e1, e2) ->
      (* Hongseok's comment: there are possibly redundant consistency
	 checks. *)
      let f pset_cur prop = 
        E.log "@..... [prune_polarity] (%a=%a) ....@.prop:%a@." pp_exp e1 pp_exp e2 pp_prop prop; 
	let is_inconsistent = 
          if positive then check_disequal prop e1 e2
	  else check_equal prop e1 e2 
	in if is_inconsistent then pset_cur else 
	    let new_prop = 
              if positive then conjoin_eq e1 e2 prop 
	      else conjoin_neq e1 e2 prop
	    in if check_inconsistency new_prop then pset_cur
	      else propset_add new_prop pset_cur
      in propset_fold f propset_empty pset 
  | BinOp (Cil.Ne, e1, e2) ->
      (* Hongseok's comment: there are possibly redundant consistency
	 checks. *)
      let f pset_cur prop = 
	let is_inconsistent = 
	  if positive then check_equal prop e1 e2 
	  else check_disequal prop e1 e2
	in if is_inconsistent then pset_cur else 
	    let new_prop = 
              if positive then conjoin_neq e1 e2 prop
	      else conjoin_eq e1 e2 prop
	    in if check_inconsistency new_prop then pset_cur
	      else propset_add new_prop pset_cur
      in propset_fold f propset_empty pset
  | BinOp (Cil.Lt, e1, e2) | BinOp(Cil.Gt, e2, e1) ->
      (* Hongseok's comment: there are possibly redundant consistency
	 checks. *)
      let f pset_cur prop = 
	let is_inconsistent = 
	  if positive then check_leq prop e2 e1 
	  else check_less prop e1 e2
	in if is_inconsistent then pset_cur else 
	    let new_prop = 
              if positive then conjoin_less e1 e2 prop
	      else conjoin_leq e2 e1 prop
	    in if check_inconsistency new_prop then pset_cur
	      else propset_add new_prop pset_cur
      in propset_fold f propset_empty pset
  | BinOp (Cil.Le, e1, e2) | BinOp(Cil.Ge, e2, e1) ->
      (* Hongseok's comment: there are possibly redundant consistency
	 checks. *)
      let f pset_cur prop = 
	let is_inconsistent = 
	  if positive then check_less prop e2 e1 
	  else check_leq prop e1 e2
	in if is_inconsistent then pset_cur else 
	    let new_prop = 
              if positive then conjoin_leq e1 e2 prop
	      else conjoin_less e2 e1 prop
	    in if check_inconsistency new_prop then pset_cur
	      else propset_add new_prop pset_cur
      in propset_fold f propset_empty pset
  | BinOp (Cil.LAnd, condition1, condition2) ->
      let pset1 = prune_polarity positive condition1 pset in
      let pset2 = prune_polarity positive condition2 pset
      in (if positive then propset_inter else propset_union) pset1 pset2
  | BinOp (Cil.LOr, condition1, condition2) ->
      let pset1 = prune_polarity positive condition1 pset in
      let pset2 = prune_polarity positive condition1 pset
      in (if positive then propset_union else propset_inter) pset1 pset2
  | BinOp _ ->
      pset
  | Lfield _ | Lindex _  ->
      pset

let prune condition pset = prune_polarity true condition pset

(** {2 Lifted Abstract Transfer Functions} *)

let lifted_rename_primed_vars pset =
  propset_map prop_rename_primed_vars pset 

let lifted_exist_quantify ids pset =
  propset_map (exist_quantify ids) pset 

let lifted_sym_exec pset instr =
  let f pset1 p = propset_union (sym_exec instr p) pset1
  in propset_fold f propset_empty pset

let lifted_compose pset1 pset2 = 
  let f pset_acc p1 =
    let g pset_acc' p2 = propset_add (prop_compose p1 p2) pset_acc'
    in propset_fold g pset_acc pset2
  in propset_fold f propset_empty pset1

