(** Symbolic Execution *)

open Propset

(** Raised when a program possily dereferences a dangling pointer. *)
exception MEMORY_ERROR

(** [ptsto_lookup (lexp,strexp,typ) offlist id] given
    [lexp|->strexp:typ] returns the expression at position [offlist]
    in [strexp], together with [strexp], if the location [offlist]
    exists in [strexp]. If the location does not exist, it constructs
    [strexp'] containing [id] at [offlist], and returns
    ([ident],[strexp']).*)
val ptsto_lookup : (Sil.exp * Sil.strexp * Sil.typ) -> (Sil.offset list) -> Ident.ident -> (Sil.exp * Sil.strexp)

(** [ptsto_update (lexp,strexp,typ) offlist exp] given
    [lexp|->strexp:typ] returns an updated [strexp] obtained by
    replacing the expression at [offlist] with [exp]. *)
val ptsto_update : (Sil.exp * Sil.strexp * Sil.typ) -> (Sil.offset list) -> Sil.exp -> Sil.strexp

(** Prune a set of propositions based on [exp=1] *)
val prune : Sil.exp -> propset -> propset

val lifted_rename_primed_vars : propset -> propset

(** Existentially quantify all identifiers in [ident list] for all
    propositions in [propset] *)
val lifted_exist_quantify : Sil.fav -> propset -> propset

(** symbolic execution on the level of sets of propositions *)
val lifted_sym_exec : propset -> Sil.instr -> propset

(** composition of two propositions *)
val lifted_compose : propset -> propset -> propset
