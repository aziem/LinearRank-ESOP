(** Functions for Propositions (i.e., Symbolic Heaps) *)

open Ident
open Sil
open Prop
open Simp

module E = Error

(** {2 Theorem Proving} *)

(** [is_root prop base_exp exp] checks whether [base_exp =
    exp.offlist] for some list of offsets [offlist]. If so, it returns
    [Some(offlist)].  Otherwise, it returns [None]. Assumes that
    [base_exp] points to the beginning of a structure, not the middle.
*)
let is_root prop base_exp exp = 
  let base_exp = exp_normalize_prop prop base_exp in
  let exp = exp_normalize_prop prop exp in
  let rec f offlist_past e = match e with
    | Var _ | Const_int _ | UnOp _ | BinOp _ | Lvar _ | Fvar _ -> 
	if (exp_equal base_exp e)
	then Some(offlist_past)
	else None
    | Cast(t,sub_exp) -> f offlist_past sub_exp
    | Lfield(sub_exp,fldname) -> f (Off_fld(fldname)::offlist_past) sub_exp
    | Lindex(sub_exp,e) -> f (Off_index(e)::offlist_past) sub_exp
  in f [] exp


(** Check whether [prop |- allocated(e)]. *)
let check_allocatedness prop e =
  let n_e = exp_normalize_prop prop e in
  let spatial_part = prop_get_sigma prop in
  let f = function
    | Hpointsto (base, _, _) -> 
        is_root prop base n_e <> None
  in List.exists f spatial_part  

(** Inconsistency checking. *)
let check_inconsistency_base prop =
  let pi = prop_get_pi prop in
  let inconsistent_ptsto _ =
    check_allocatedness prop (Const_int 0) in
  let inconsistent_two_hpreds _ =
    let rec f e sigma_seen = function
      | [] -> false
      | (Hpointsto (e1,_,_) as hpred) :: sigma_rest ->
          if exp_equal e1 e then true
          else f e (hpred::sigma_seen) sigma_rest
    in
    let rec check sigma_seen = function
      | [] -> false
      | (Hpointsto (e1,_,_) as hpred) :: sigma_rest ->
	  if (f e1 [] (sigma_seen@sigma_rest)) then true
	  else check (hpred::sigma_seen) sigma_rest
    in
    let sigma = prop_get_sigma prop 
    in check [] sigma in
  let inconsistent_atom = function
    | Aeq (e1,e2) -> (match e1,e2 with
	| Const_int n, Const_int m -> n<>m
	| _ -> false)
    | Aneq (e1,e2) -> (match e1,e2 with
	| Const_int n, Const_int m -> n=m
	| _ -> (exp_compare e1 e2 = 0))
    | Aless (e1,e2) -> (match e1,e2 with
	| Const_int n, Const_int m -> n>=m
	| _ -> false)
    | Aleq (e1,e2) -> (match e1,e2 with
	| Const_int n, Const_int m -> n>m
	| _ -> false)
    in 
    if (!Config.prover = 1) then 
        inconsistent_ptsto () || inconsistent_two_hpreds () || (simplify pi) 
    else if (!Config.prover = 0) then 
        inconsistent_ptsto () || inconsistent_two_hpreds () || List.exists inconsistent_atom pi 
    else if (!Config.prover = 2)  then
        inconsistent_ptsto () || inconsistent_two_hpreds () || (z3 pi) 
    else false
(** Inconsistency checking. *)
let check_inconsistency prop =
  check_inconsistency_base prop 

(** Check [prop |- e1=e2]. *)
let check_equal prop e1 e2 = 
  let pi = prop_get_pi prop in
  let n_e1 = exp_normalize_prop prop e1 in
  let n_e2 = exp_normalize_prop prop e2 
  in if (exp_compare e1 e2 = 0) then true
    else 
      let eq = Aeq(n_e1,n_e2) in
      let n_eq = atom_normalize_prop prop eq 
      in List.exists (atom_equal n_eq) pi



(** Check whether [prop |- e1!=e2]. *)
let check_disequal prop e1 e2 =
  let pi = prop_get_pi prop in
  let spatial_part = prop_get_sigma prop in
  let n_e1 = exp_normalize_prop prop e1 in
  let n_e2 = exp_normalize_prop prop e2 in
  let does_pi_imply_disequal ne ne' = 
    let diseq = Aneq(ne,ne') in
    let n_diseq = atom_normalize_prop prop diseq 
    in List.exists (atom_equal n_diseq) pi 
  in  
  let neq_spatial_part _ =
    let rec f sigma_irrelevant e = function
      | [] -> None
      | Hpointsto (base, _, _) as hpred :: sigma_rest -> 
          (match is_root prop base e with 
	      | None -> 
    let sigma_irrelevant' = hpred :: sigma_irrelevant
    in f sigma_irrelevant' e sigma_rest
       | Some _ -> 
                let sigma_irrelevant' = (List.rev sigma_irrelevant) @ sigma_rest 
    in Some (true, sigma_irrelevant')) in
    let f_null_check sigma_irrelevant e sigma_rest =
      if not (exp_equal e (Const_int 0)) then f sigma_irrelevant e sigma_rest
      else 
   let sigma_irrelevant' = (List.rev sigma_irrelevant) @ sigma_rest
   in Some (false, sigma_irrelevant') 
    in match f_null_check [] n_e1 spatial_part with
      | None -> false 
      | Some (e1_allocated, spatial_part_leftover) -> 
          (match f_null_check [] n_e2 spatial_part_leftover with
            | None -> false
     | Some ((e2_allocated : bool), _) -> e1_allocated || e2_allocated) 
  in
  let neq_pure_part _ = 
    does_pi_imply_disequal n_e1 n_e2
  in 
    (neq_pure_part ()) || (neq_spatial_part ())

(** [prop|- e1 < e2] *)
let check_less prop e1 e2 = 
  let ne1 = exp_normalize_prop prop e1 in
  let ne2 = exp_normalize_prop prop e2 in
  let atom = Aless(ne1,ne2) in
  let pi = prop_get_pi prop
  in List.exists (atom_equal atom) pi 

(** [prop|- e1 <= e2] *)
let check_leq prop e1 e2 = 
  let ne1 = exp_normalize_prop prop e1 in
  let ne2 = exp_normalize_prop prop e2 in
  let f atom = 
    atom_equal (Aleq(ne1,ne2)) atom || atom_equal (Aless(ne1,ne2)) atom in
  let pi = prop_get_pi prop 
  in List.exists f pi
