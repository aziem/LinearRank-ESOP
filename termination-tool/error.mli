(** Print if log is active. *)
val log : ('a, Format.formatter, unit) format -> 'a

(** Print. *)
val err : ('a, Format.formatter, unit) format -> 'a
