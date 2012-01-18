(** Functions for Propositions (i.e., Symbolic Heaps) *)

open Sil
open Prop
open Prover

module E = Error

(** {2 Sets of Propositions} *)

module PropSet =
  Set.Make(struct
    type t = prop 
    let compare = prop_compare
  end)

(** Sets of propositions. *)
type propset = PropSet.t 

(** Singleton set. *)
let propset_singleton p = 
  PropSet.add p PropSet.empty

(** Set union. *)
let propset_union = PropSet.union

(** Set membership *)
let propset_mem = PropSet.mem 

(** Set intersection *)
let propset_inter = PropSet.inter

let propset_add p pset = 
  if check_inconsistency p then pset
  else PropSet.add p pset

(** Set difference. *)
let propset_diff = PropSet.diff

let propset_empty = PropSet.empty

(** Set emptiness check. *)
let propset_is_empty = PropSet.is_empty

(** Size of the set *)
let propset_size = PropSet.cardinal

let proplist2propset plist =
  List.fold_right propset_add plist propset_empty

let propset2proplist = PropSet.elements

(** Apply function to all the elements of [propset], removing those where it returns [None]. *)
let propset_map_option f pset =
  let plisto = List.map f (propset2proplist pset) in
  let plisto = List.filter (function | Some _ -> true | None -> false) plisto in
  let plist = List.map (function Some p -> p | None -> assert false) plisto
  in proplist2propset plist

(** Apply function to all the elements of [propset]. *)
let propset_map f pset =
  proplist2propset (List.map f (propset2proplist pset))

(** Filter *)
let propset_filter = PropSet.filter

(** [propset_fold f pset a] computes [f (... (f (f a p1) p2) ...) pn]
    where [p1 ... pN] are the elements of pset, in increasing order. *)
let propset_fold f a pset  =
  let l = propset2proplist pset
  in List.fold_left f a l

(** [propset_iter f pset] computes (f p1;f p2;..;f pN)
    where [p1 ... pN] are the elements of pset, in increasing order. *)
let propset_iter = PropSet.iter 

let propset_subseteq = PropSet.subset


(** {2 Pretty print} *)

open Format

(** Pretty print a set of propositions. *)
let pp_propset f pset =
  let rec pp_seq_newline n f = function
    | [] -> ()
    | [x] -> fprintf f "PROP %d: %a" n pp_prop x
    | x::l -> fprintf f "PROP %d: %a@.@.%a" n pp_prop x (pp_seq_newline (n+1)) l in
  let plist = propset2proplist pset 
  in pp_seq_newline 1 f plist
