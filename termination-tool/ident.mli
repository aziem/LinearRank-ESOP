(** Identifiers: program variables and logical variables *)

(** Program and logical variables. *)
type ident

(** Names used to replace strings. *)
type name

(** Kind of identifiers. *)
type kind

(** hash table for a type environment *)
module NameHash : Hashtbl.S with type key = name

(** Convert a string to a name. *)
val string_to_name : string -> name

(** Convert a name to a string. *)
val name_to_string : name -> string

(** Name of the identifier. *)
val ident_name : ident -> name

(** Kind of the identifier. *)
val ident_kind : ident -> kind

(** Return a footprint identifier that is deterimined the given name.
    This identifier is used to keep the initial value of program
    variable [name]. *)
val get_default_footprint_ident : name -> ident

(** Create a fresh normal identifier with the given name. *)
val create_fresh_normal_ident : name -> ident

(** Create a fresh primed identifier with the given name. *)
val create_fresh_primed_ident : name -> ident

(** Check whether an identifier is primed or not. *)
val ident_is_primed : ident -> bool

(** Convert a primed ident into a nonprimed one, keeping the stamp. *)
val make_ident_unprimed : ident -> ident

(** Get the stamp of the identifier *)
val ident_get_stamp: ident -> int

(** Set the stamp of the identifier *)
val ident_set_stamp: ident -> int -> ident

(** {2 Comparision Functions} *)

(** Equality police: only defined on integers. *)
val (=) : int -> int -> bool

(** Compare police: generic compare disabled. *)
val compare : unit

(** Efficient comparison for integers *)
val int_compare : int -> int -> int

(** Comparison for names. *)
val name_compare : name -> name -> int

(** Equality for names. *)
val name_equal : name -> name -> bool

(** Equality for kind. *)
val kind_equal : kind -> kind -> bool

(** Comparison for identifiers. *)
val ident_compare : ident -> ident -> int

(** Equality for identifiers. *)
val ident_equal : ident -> ident -> bool

(** Comparison for lists of identities *)
val ident_list_compare : ident list -> ident list -> int

(** Equality for lists of identities *)
val ident_list_equal : ident list -> ident list -> bool

(** {2 Pretty Printing} *)

(** Convert an identified to a string. *)
val ident_to_rankfinder_string : ident -> string

(** Pretty print a name. *)
val pp_name : Format.formatter -> name -> unit

(** Pretty print an identifier. *)
val pp_ident : Format.formatter -> ident -> unit

(** Pretty print a list of identifiers. *)
val pp_ident_list : Format.formatter -> ident list -> unit

(** Pretty print a list of names. *)
val pp_name_list : Format.formatter -> name list -> unit


