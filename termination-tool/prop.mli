(** Functions for Propositions (i.e., Symbolic Heaps) *)

open Ident
open Sil

(** Proposition. *)
type prop

(** {2 Basic Functions for propositions} *)

(** Compare propositions *)
val prop_compare : prop -> prop -> int

(** Checks the equality of two propositions *)
val prop_equal : prop -> prop -> bool

(** Pretty print a substitution. *)
val pp_sub : Format.formatter -> subst -> unit

(** Pretty print a sigma. *)
val pp_sigma : Format.formatter -> Sil.hpred list -> unit

(** Pretty print a proposition. *)
val pp_prop : Format.formatter -> prop -> unit

(** Compute free non-program variables of pi *)
val pi_fav_add : fav -> atom list -> unit

(** Compute free non-program variables of sigma *)
val sigma_fav_add : fav -> hpred list -> unit

val sigma_fav : hpred list -> fav

(** returns free non-program variables that are used to express
the contents of stack variables *)
val sigma_fav_in_pvars_add : fav -> hpred list -> unit

(** Compute free non-program variables of prop *)
val prop_fav_add : fav -> prop -> unit

val prop_fav: prop -> fav

(** Apply substitution for pi *)
val pi_sub : subst -> atom list -> atom list

(** Apply subsitution for sigma *)
val sigma_sub : subst -> hpred list -> hpred list


(** {2 Normalization} *)

(** Normalize [exp] using the pure part of [prop].  Later, we should
    change this such that the normalization exposes offsets of [exp]
    as much as possible. *)
val exp_normalize_prop : prop -> exp -> exp

val atom_normalize_prop : prop -> atom -> atom

val hpred_normalize_prop : prop -> hpred -> hpred

val sigma_normalize_prop : prop -> hpred list -> hpred list

(** {2 Queries about propositions} *)

(** Check if the proposition is pure *)
val prop_is_pure : prop -> bool


(** {2 Functions for changing and generating propositions} *)

(** Construct a pointsto. *)
val mk_ptsto :  exp -> strexp -> typ -> hpred

(** Construct a points-to predicate for an expression using [name] as
    base for fresh identifiers. *)
val mk_ptsto_exp : name -> exp * typ * exp option -> hpred

(** Construct a points-to predicate for a single program variable. *)
val mk_ptsto_lvar : pvar * typ * exp option -> hpred 


(** Proposition [true /\ emp] at [int]. *)
val prop_emp : int -> prop

(** Conjoin a heap predicate by separating conjunction. *)
val prop_hpred_star : prop -> hpred -> prop

(** Conjoin a list of heap predicates by separating conjunction *)
val prop_sigma_star : prop -> hpred list -> prop

val prop_addvisited : prop -> int -> prop

val prop_set_wf : prop -> bool -> prop

val prop_is_wf : prop -> bool

(** Conjoin a pure atomic predicate by normal conjunction. *)
val prop_atom_and : prop -> atom -> prop

(** Conjoin [exp1]=[exp2] with a symbolic heap [prop]. *)
val conjoin_eq :  exp -> exp -> prop -> prop

(** Conjoin [exp1]!=[exp2] with a symbolic heap [prop]. *)
val conjoin_neq : exp -> exp -> prop -> prop

(** Conjoin [exp1]<[exp2] with a symbolic heap [prop]. *)
val conjoin_less : exp -> exp -> prop -> prop

(** Conjoin [exp1]!=[exp2] with a symbolic heap [prop]. *)
val conjoin_leq : exp -> exp -> prop -> prop

(** Return the statement id of [prop] *)
val prop_get_sid : prop -> int

(** Return the equalities in the proposition *)
val prop_get_equalities : prop -> (exp * exp) list

(** Return the sub part of [prop]. *)
val prop_get_sub : prop -> subst

(** Return the pi part of [prop]. *)
val prop_get_pi : prop -> atom list

(** Return the pure part of [prop]. *)
val prop_get_pure : prop -> atom list

val prop_get_visited : prop -> int list

val prop_set_visited : prop -> int list -> prop

(** Replace the pi part of [prop]. *)
val prop_replace_pi : atom list -> prop -> prop

(** Return the sigma part of [prop] *)
val prop_get_sigma : prop -> hpred list

(** Replace the sigma part of [prop] *)
val prop_replace_sigma : hpred list -> prop -> prop

(** Initialize proposition for execution given formal and global parameters. *)
val prop_init_formals_locals :  (pvar * typ * exp option) list -> (pvar * typ * exp option) list -> prop -> prop

(** Canonicalize the names of primed variables. *)
val prop_rename_primed_vars : prop -> prop

(** Rename [ident] in [prop] by a fresh primed identifier *)
val prop_make_id_primed : Ident.ident -> prop -> prop

(** {2 Functions for existentially quantifying and unquantifying variables} *)

(** Existentially quantify the [ids] in [prop]. *)
val exist_quantify : fav -> prop -> prop

(** Read two propositions as relations and compose them.  Assume that
    the same set of program variables are allocated in the given
    propositions *)
val prop_compose : prop -> prop -> prop

(** {2 Prop iterators} *)

(** Iterator over the sigma part. Each iterator has a current [hpred]. *)
type 'a prop_iter

(** Create an iterator, return None if sigma part is empty. *)
val prop_iter_create : prop -> ('a prop_iter) option

(** Return the prop associated to the iterator. *)
val prop_iter_to_prop : 'a prop_iter -> prop

(** Remove the current element from the iterator, and return the prop
    associated to the resulting iterator. *)
val prop_iter_remove_curr_then_to_prop : 'a prop_iter -> prop

(** Return the current hpred and state. *)
val prop_iter_current : 'a prop_iter -> (hpred * 'a option)

(** Return the next iterator. *)
val prop_iter_next : 'a prop_iter -> 'a prop_iter option

(** Remove the current hpred and return the next iterator. *)
val prop_iter_remove_curr_then_next : 'a prop_iter -> 'a prop_iter option

(** Update the current element of the iterator. *)
val prop_iter_update_current : 'a prop_iter -> hpred -> 'a prop_iter

(** Scan sigma to find an [hpred] satisfying the filter function. *)
val prop_iter_find : 'a prop_iter -> (hpred -> 'a option) -> 'a prop_iter option

(** Update the current element of the iterator by a nonempty list of
    elements. *)
val prop_iter_update_current_by_list : 'a prop_iter -> hpred list -> 'a prop_iter

(** Set the state of an iterator *)
val prop_iter_set_state : 'a prop_iter -> 'b -> 'b prop_iter

(** Rename [ident] in [iter] by a fresh primed identifier *)
val prop_iter_make_id_primed : Ident.ident -> 'a prop_iter -> 'a prop_iter

(** Collect garbage fields. *)
val prop_iter_gc_fields :  'a prop_iter -> 'a prop_iter
