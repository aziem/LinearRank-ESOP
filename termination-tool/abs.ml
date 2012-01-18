(** Symbolic Execution *)

open Ident
open Sil
open Prop
open Propset
open Prover
open Rankfinder

module E = Error


let list_intersect compare l1 l2 =
  let l1_sorted = List.sort compare l1 in
  let l2_sorted = List.sort compare l2 in
  let rec f l1 l2 = match l1, l2 with
    | ([],_) | (_,[]) -> false
    | (x1::l1', x2::l2') -> 
	let x_comparison = compare x1 x2
	in if x_comparison = 0 then true
	  else if x_comparison = -1 then f l1' l2
	  else f l1 l2'
  in f l1_sorted l2_sorted



(* ================ Start of Main Abstraction Functions =============== *)

let abstract_pure_part p =
  let pi = prop_get_pi p in
  let rec f pi_included = function
    | [] -> List.rev pi_included | (Aeq(e1,e2) as a)::pi_rest -> 
        if exp_equal e1 e2 
        then f pi_included pi_rest 
	else f (a::pi_included) pi_rest
    | (Aneq(e1,e2) as a):: pi_rest ->
	let p' = prop_replace_pi pi_included p 
	in if check_disequal p' e1 e2 
          then f pi_included pi_rest 
	  else f (a::pi_included) pi_rest 
    | (Aless(e1,e2) as a):: pi_rest ->
	let p' = prop_replace_pi pi_included p 
	in if check_less p' e1 e2 
          then f pi_included pi_rest 
	  else f (a::pi_included) pi_rest 
    | (Aleq(e1,e2) as a):: pi_rest ->
	let p' = prop_replace_pi pi_included p 
	in if check_leq p' e1 e2 
          then f pi_included pi_rest 
	  else f (a::pi_included) pi_rest in
  let new_pi = f [] pi in
  let new_p = prop_replace_pi new_pi p 
  in new_p	   


let abstract sid p = 
  let p' = abstract_pure_part p in 
  let p'' = match rankfinder sid p' with
    | None -> p'
    | Some (p'') -> p'' in
  let ren_p = prop_rename_primed_vars p''
  in ren_p



let lifted_abstract sid pset =
  let f p =
    if check_inconsistency p then None
    else Some (abstract sid p) in
  let abstracted_pset = propset_map_option f pset 
  in abstracted_pset

(* ================ End of Main Abstraction Functions =============== *)
