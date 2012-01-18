(** The Smallfoot Intermediate Language *)

open Ident

(** Field names. *)
type fieldname = name

(** Nams for named types. *)
type typename = name 

(** {2 Programs and Types} *)

type pvar

(** Names for functions. *)
type funname = name

(** Types for sil (structured) expressions. *)
type typ =
    | Tvar of typename  (** named type *)
    | Tint (** integer type *)
    | Tvoid (** void type *)
    | Tfun (** function type *)
    | Tptr of typ (** pointer type *)
    | Tstruct of (fieldname * typ) list (** structure type *)
    | Tarray of typ * int (** array type with fixed size *)

(** Program expressions. *)
type exp =
    | Var of ident (** pure variable: it is not an lvalue *)
    | Const_int of int  (** integer constants *)
    | Cast of typ * exp  (** type cast *)
    | UnOp of Cil.unop * exp (** unary operator *)
    | BinOp of Cil.binop * exp * exp (** binary operator *)
    | Lvar of pvar  (** the address of a program variable *)
    | Fvar of funname (** the name of a function *)
    | Lfield of exp * fieldname (** a field offset *)
    | Lindex of exp * exp (** an array index offset: [exp1\[exp2\]] *)

(** An instruction. *)
type instr =
    | Letderef of ident * exp * typ * Cil.location (** declaration [let x = *lexp:typ] *)
    | Set of exp * typ * exp * Cil.location (** assignment [*lexp1:typ = exp2] *)
    | Call of (exp * typ * typ) option * exp * (exp*typ) list * Cil.location
               (** function call [*lexp1 = (typ)exp2(exp(typ) list)] *) 

(** Offset for an lvalue. *)
type offset = Off_fld of fieldname | Off_index of exp

(** {2 Components of Propositions} *)

(** Structured expressions represent a value of structured type, such
    as an array or a struct. *)
type strexp =
    | Eexp of exp  (** Base case: normal expression *)
    | Estruct of (fieldname * strexp) list  (** C structure *)
    | Earray of int * (exp * strexp) list  (** Array of fixed size. *)

(** an atom is a pure atomic formula *)
type atom =
    | Aeq of exp * exp (** = *)
    | Aneq of exp * exp (** != *)
    | Aless of exp * exp (** < *)
    | Aleq of exp * exp (** <= *)


(** an atomic heap predicate *)

type hpred =
    | Hpointsto of exp * strexp * typ  (** represents exp|->strexp:typ *)



(** {2 Type Environment} *)

(** Look up a name in the global type environment. *)
val tenv_lookup : typename -> typ option

(** Add a (name,typ) pair to the global type environment. *)
val tenv_add : typename -> typ -> unit

(** {2 Comparison Functions} *)

val pvar_get_name : pvar -> name

val pvar_compare : pvar -> pvar -> int 

val pvar_equal : pvar -> pvar -> bool

val pvar_list_compare : pvar list -> pvar list -> int

val pvar_list_equal : pvar list -> pvar list -> bool

(** Comparision for fieldnames. *)
val fld_compare : fieldname -> fieldname -> int

(** Equality for fieldnames. *)
val fld_equal : fieldname -> fieldname -> bool

(** Comparision for types. *)
val typ_compare : typ -> typ -> int

(** Equality for ty  let stack = prop_get_current_stack p1 in
  let stack_sub = 
    let p2' = ... in
    let p = ...
    in ppes. *)
val typ_equal : typ -> typ -> bool

val unop_equal : Cil.unop -> Cil.unop -> bool

val binop_equal : Cil.binop -> Cil.binop -> bool

val exp_compare : exp -> exp -> int

val exp_equal : exp -> exp -> bool

val atom_compare : atom -> atom -> int

val atom_equal : atom -> atom -> bool

val strexp_compare : strexp -> strexp -> int

val strexp_equal : strexp -> strexp -> bool

val hpred_compare : hpred -> hpred -> int

val hpred_equal : hpred -> hpred -> bool

val fld_strexp_compare : fieldname * strexp -> fieldname * strexp -> int

val fld_strexp_list_compare : (fieldname * strexp) list  -> (fieldname * strexp) list -> int

val exp_strexp_compare : exp * strexp -> exp * strexp -> int

(** {2 Pretty Printing} *)

(** Pretty print a type. *)
val pp_typ : Format.formatter -> typ -> unit

(** Pretty print an expression. *)
val pp_exp : Format.formatter -> exp -> unit

(** Pretty print an instruction. *)
val pp_instr : Format.formatter -> instr -> unit

(** Pretty print a list of instructions. *)
val pp_instr_list : Format.formatter -> instr list -> unit

(** Pretty print an atom. *)
val pp_atom : Format.formatter -> atom -> unit

(** Pretty print a strexp. *)
val pp_sexp : Format.formatter -> strexp -> unit

(** Pretty print a hpred. *)
val pp_hpred : Format.formatter -> hpred -> unit

(** Pretty print a hpred. *)
val pp_hpred_list : Format.formatter -> hpred list -> unit

(** {2 Functions for computing program variables} *)

val exp_fpv : exp -> pvar list

val strexp_fpv : strexp -> pvar list

val atom_fpv : atom -> pvar list

val hpred_fpv : hpred -> pvar list


(** {2 Functions for computing free non-program variables} *)

(** Type of free variables. These include primed, normal and footprint variables. We keep a count of how many types the variables appear. *)
type fav

(** Pretty print a fav. *)
val pp_fav : Format.formatter -> fav -> unit

(** Create a new [fav]. *)
val fav_new : unit -> fav

(** Emptyness check. *)
val fav_is_empty : fav -> bool

(** Membership test fot [fav] *)
val fav_mem : fav -> ident -> bool

(** Convert a list to a fav. *)
val fav_from_list : ident list -> fav

(** Convert a [fav] to a list of identifiers without repetitions. *)
val fav_to_list : fav -> ident list

(** Copy a [fav]. *)
val fav_copy : fav -> fav

(** Turn a xxx_fav_add function into a xxx_fav function *)
val fav_imperative_to_functional : (fav -> 'a -> unit) -> 'a -> fav

(** [fav_filter_ident fav f] only keeps [id] if [f id] is true. *)
val fav_filter_ident : fav -> (ident->bool) -> unit

(** Like [fav_filter_ident] but return a copy. *)
val fav_copy_filter_ident : fav -> (ident->bool) -> fav

(** [fav_subset_ident fav1 fav2] returns true if every ident in [fav1]
    is in [fav2].*)
val fav_subset_ident : fav -> fav -> bool

(** [exp_fav_add fav exp] extends [fav] with the free variables of [exp] *)
val exp_fav_add : fav -> exp -> unit

val exp_fav : exp -> fav

val ident_in_exp : ident -> exp -> bool

val strexp_fav_add : fav -> strexp -> unit

val atom_fav_add : fav -> atom -> unit

val atom_fav: atom -> fav

val hpred_fav_add : fav -> hpred -> unit

(** {2 Substitution} *)

type subst

(** Create a substitution from a list of pairs. *)
val sub_of_list : (ident * exp) list -> subst

(** Convert a subst to a list of pairs. *)
val sub_to_list : subst -> (ident * exp) list

(** The empty substitution. *)
val sub_empty : subst

(** Comparison for substitutions. *)
val sub_compare : subst -> subst -> int

(** Equality for substitutions. *) 
val sub_equal : subst -> subst -> bool

(** Join two substitutions into one. *)
val sub_join : subst -> subst -> subst

(** [sub_find filter sub] returns the expression associated to the first identifier that satisfies [filter]. Raise [Not_found] if there isn't one. *)
val sub_find : (ident->bool) -> subst -> exp

(** [sub_filter filter sub] restricts the domain of [sub] to the
    identifiers satisfying [filter]. *)
val sub_filter : (ident -> bool) -> subst -> subst

(** [sub_range_partition filter sub] partitions [sub] according to
    whether range expressions satisfy [filter]. *)
val sub_range_partition : (exp -> bool) -> subst -> subst*subst

(** [sub_domain_partition filter sub] partitions [sub] according to
    whether domain identifiers satisfy [filter]. *)
val sub_domain_partition : (ident -> bool) -> subst -> subst*subst

(** Return the list of expressions in the range of the substitution. *)
val sub_range : subst -> exp list

(** [sub_range_map f sub] applies [f] to the expressions in the range of [sub]. *)
val sub_range_map : (exp -> exp) -> subst-> subst

(** Extend substitution and return [None] if not possible. *)
val extend_sub : subst -> ident -> exp -> subst option

(** Free auxilary variables in the domain and range of the
    substitution. *)
val sub_fav_add : fav -> subst -> unit

(** Free or bound auxilary variables in the domain and range of the
    substitution. *)
val sub_av_add : fav -> subst -> unit

val exp_sub : subst -> exp -> exp

val strexp_sub : subst -> strexp -> strexp

val atom_sub : subst -> atom -> atom

val hpred_sub : subst -> hpred -> hpred


(** {2 Functions for constructing or destructing entities in this module} *)

val mk_pvar : name -> Cil.fundec -> pvar

(** Compute the offset list of an expression *)
val exp_get_offsets : exp -> offset list
