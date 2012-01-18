(** Abstraction *)

open Propset

(** abstract each proposition in [propset] *)
val lifted_abstract : int -> propset -> propset
