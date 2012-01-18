(** Functions for Theorem Proving *)

open Ident
open Sil
open Prop

(** Check [prop |- exp1=exp2]. *)
val check_equal : prop -> exp -> exp -> bool

(** Check whether [prop |- exp1!=exp2]. *)
val check_disequal : prop -> exp -> exp -> bool

(** Check whether [prop|- e1 < e2] *)
val check_less : prop -> exp -> exp -> bool

(** Check whether [prop|- e1 <= e2] *)
val check_leq : prop -> exp -> exp -> bool

(** Inconsistency checking. *)
val check_inconsistency : prop -> bool
  
(** Check whether [prop |- allocated(exp)]. *)
val check_allocatedness : prop -> exp -> bool


(** [is_root prop base_exp exp] checks whether [base_exp =
    exp.offlist] for some list of offsets [offlist]. If so, it returns
    [Some(offlist)].  Otherwise, it returns [None]. Assumes that
    [base_exp] points to the beginning of a structure, not the middle. *)
val is_root : prop -> exp -> exp -> offset list option
