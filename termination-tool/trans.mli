(** Translation from cil to sil *)

(** list of instructions to translate impure expressions, and the list
    of local variables generated *)
type temp_list = Ident.ident list * Sil.instr list

val trans_typ : Ident.name list -> Cil.typ -> Sil.typ
val trans_exp : Cil.fundec -> Cil.exp -> temp_list * Sil.exp
val trans_lval : Cil.fundec -> Cil.lval -> temp_list * Sil.exp
val trans_explist : Cil.fundec -> Cil.exp list -> temp_list * Sil.exp list
val trans_typeinfo : Ident.name list -> Cil.typeinfo -> Sil.typ
val trans_instr : Cil.fundec -> Cil.instr -> temp_list
