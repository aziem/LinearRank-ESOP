(** The Smallfoot Intermediate Language *)

open Ident

(** {2 Programs and Types} *)

(** Names for fields. *)
type fieldname = name

(** Names for named types. *)
type typename = name

(** Names for program variables. *)
type pvar = {pv_name: name; pv_funid: int; pv_funname: string}

(** Names for functions. *)
type funname = name

(** types for sil (structured) expressions *)
type typ =
    | Tvar of typename  (** named type *)
    | Tint (** integer type *)
    | Tvoid (** void type *)
    | Tfun (** function type *)
    | Tptr of typ (** pointer type *)
    | Tstruct of (fieldname * typ) list (** structure type *)
    | Tarray of typ * int (** array type with fixed size *)

(** program expressions *)
type exp =
    | Var of ident (** pure variable: it is not an lvalue *)
    | Const_int of int  (** integer constants *)
    | Cast of typ * exp  (** type cast *)
    | UnOp of Cil.unop * exp (** unary operator *)
    | BinOp of Cil.binop * exp * exp (** binary operator *)
    | Lvar of pvar  (** the address of a program variable *)
    | Fvar of funname (** the name of a function *)
    | Lfield of exp * fieldname (** a field offset *)
    | Lindex of exp * exp (** an array index offset: exp1[exp2] *)

(** An instruction. *)
type instr =
    | Letderef of ident * exp * typ * Cil.location (** declaration [let x = *lexp:typ] *)
    | Set of exp * typ * exp * Cil.location (** assignment [*lexp1:typ = exp2] *)
    | Call of (exp * typ * typ) option * exp * (exp*typ) list * Cil.location
               (** function call [*lexp1 = (typ)exp2(exp(typ) list)] *) 

(** offset for an lvalue *)
type offset = Off_fld of fieldname | Off_index of exp

(** {2 Components of Propositions} *)

(** structured expressions represent a value of structured type, such as an array or a struct. *)
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

(** {2 Comparision Functions} *)

let pvar_get_name pv = pv.pv_name

let fundec_hash = Hashtbl.create 10

let fundec_to_int (fundec:Cil.fundec) : int =
  try Hashtbl.find fundec_hash fundec
  with Not_found ->
    let n = Hashtbl.length fundec_hash in
    let _ = Hashtbl.add fundec_hash fundec n
    in n

let pvar_compare pv1 pv2 =
  let n = name_compare pv1.pv_name pv2.pv_name 
  in if n<>0 then n else int_compare pv1.pv_funid pv2.pv_funid

let pvar_equal pvar1 pvar2 =
  pvar_compare pvar1 pvar2 = 0

let rec pvar_list_compare pvl1 pvl2 = match pvl1,pvl2 with
  | [],[] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | pv1::l1, pv2::l2 ->
      let n = pvar_compare pv1 pv2
      in if n<>0 then n
	else pvar_list_compare l1 l2

let pvar_list_equal pvl1 pvl2 = 
  (pvar_list_compare pvl1 pvl2 = 0)

let funname_compare = name_compare

let funname_equal fname1 fname2 = (funname_compare fname1 fname2 = 0)

let fld_compare (fld1 : fieldname) fld2 = name_compare fld1 fld2

let fld_equal fld1 fld2 = fld_compare fld1 fld2 = 0

(** Comparision for types. *)
let rec typ_compare t1 t2 =
  if t1==t2 then 0 else match t1,t2 with
  | Tvar s1, Tvar s2 -> name_compare s1 s2
  | Tvar _, _ -> -1
  | _, Tvar _ -> 1
  | Tint, Tint -> 0
  | Tint, _ -> -1
  | _, Tint -> 1
  | Tvoid, Tvoid -> 0
  | Tvoid, _ -> -1
  | _, Tvoid -> 1
  | Tfun, Tfun -> 0
  | Tfun, _ -> -1
  | _, Tfun -> 1
  | Tptr t1', Tptr t2' ->
      typ_compare t1' t2'
  | Tptr _, _ -> -1
  | _, Tptr _ -> 1
  | Tstruct ntl1, Tstruct ntl2 ->
      fld_typ_list_compare ntl1 ntl2
  | Tstruct _, _ -> -1
  | _, Tstruct _ -> 1
  | Tarray (t1,n1), Tarray (t2,n2) ->
      let n = typ_compare t1 t2
      in if n<>0 then n
	else int_compare n1 n2

and fld_typ_compare (f1,t1) (f2,t2) =
  let n = fld_compare f1 f2
  in if n<>0 then n
    else typ_compare t1 t2

and fld_typ_list_compare ftl1 ftl2 = match ftl1,ftl2 with
  | [],[] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | ft1::l1, ft2::l2 ->
      let n = fld_typ_compare ft1 ft2
      in if n<>0 then n
	else fld_typ_list_compare l1 l2

let typ_equal t1 t2 = 
  (typ_compare t1 t2 = 0)

let unop_compare o1 o2 = match o1,o2 with
  | Cil.Neg, Cil.Neg -> 0
  | Cil.Neg, _ -> -1
  | _,  Cil.Neg -> 1
  |  Cil.BNot,  Cil.BNot -> 0
  |  Cil.BNot, _ -> -1
  | _,  Cil.BNot -> 1
  |  Cil.LNot, Cil.LNot -> 0

let unop_equal o1 o2 = unop_compare o1 o2 = 0

let binop_compare o1 o2  = match o1,o2 with
  | Cil.PlusA, Cil.PlusA -> 0
  | Cil.PlusA, _ -> -1
  | _, Cil.PlusA -> 1
  | Cil.PlusPI, Cil.PlusPI -> 0
  | Cil.PlusPI, _ -> -1
  | _, Cil.PlusPI -> 1
  | Cil.IndexPI, Cil.IndexPI -> 0
  | Cil.IndexPI, _ -> -1
  | _, Cil.IndexPI -> 1
  | Cil.MinusA, Cil.MinusA -> 0
  | Cil.MinusA, _ -> -1
  | _, Cil.MinusA -> 1
  | Cil.MinusPI, Cil.MinusPI -> 0
  | Cil.MinusPI, _ -> -1
  | _, Cil.MinusPI -> 1
  | Cil.MinusPP, Cil.MinusPP -> 0
  | Cil.MinusPP, _ -> -1
  | _, Cil.MinusPP -> 1
  | Cil.Mult, Cil.Mult -> 0
  | Cil.Mult, _ -> -1
  | _, Cil.Mult -> 1
  | Cil.Div, Cil.Div -> 0
  | Cil.Div,_ -> -1
  | _, Cil.Div -> 1
  | Cil.Mod, Cil.Mod -> 0
  | Cil.Mod, _ -> -1
  | _, Cil.Mod -> 1
  | Cil.Shiftlt, Cil.Shiftlt -> 0
  | Cil.Shiftlt, _ -> -1
  | _, Cil.Shiftlt -> 1
  | Cil.Shiftrt, Cil.Shiftrt -> 0
  | Cil.Shiftrt, _ -> -1
  | _, Cil.Shiftrt -> 1
  | Cil.Lt, Cil.Lt -> 0
  | Cil.Lt, _ -> -1
  | _, Cil.Lt -> 1
  | Cil.Gt, Cil.Gt -> 0
  | Cil.Gt, _ -> -1
  | _, Cil.Gt -> 1
  | Cil.Le, Cil.Le -> 0
  | Cil.Le, _ -> -1
  | _, Cil.Le -> 1
  | Cil.Ge, Cil.Ge -> 0
  | Cil.Ge, _ -> -1
  | _, Cil.Ge -> 1
  | Cil.Eq, Cil.Eq -> 0
  | Cil.Eq, _ -> -1
  | _, Cil.Eq -> 1
  | Cil.Ne, Cil.Ne -> 0
  | Cil.Ne, _ -> -1
  | _, Cil.Ne -> 1
  | Cil.BAnd, Cil.BAnd -> 0
  | Cil.BAnd, _ -> -1
  | _, Cil.BAnd -> 1
  | Cil.BXor, Cil.BXor -> 0
  | Cil.BXor, _ -> -1
  | _, Cil.BXor -> 1
  | Cil.BOr, Cil.BOr -> 0
  | Cil.BOr, _ -> -1
  | _, Cil.BOr -> 1
  | Cil.LAnd, Cil.LAnd -> 0
  | Cil.LAnd, _ -> -1
  | _, Cil.LAnd -> 1
  | Cil.LOr, Cil.LOr -> 0

let binop_equal o1 o2 = binop_compare o1 o2 = 0

(** Compare epressions. Variables come before other expressions. *)
let rec exp_compare (e1 : exp) (e2 : exp) : int  =
  match (e1,e2) with
    | (Var (id1), Var(id2)) -> 
        ident_compare id2 id1
    | (Var _, _) -> -1 
    | (_, Var _) -> 1
    | Const_int n1, Const_int n2 -> int_compare n1 n2
    | Const_int _, _ -> -1
    | _, Const_int _ -> 1
    | Cast (t1,e1), Cast(t2,e2) ->
	let n = exp_compare e1 e2
	in if n<>0 then n
	  else typ_compare t1 t2
    | Cast _, _ -> -1
    | _, Cast _ -> 1
    | UnOp (o1,e1), UnOp (o2,e2) ->
	let n = unop_compare o1 o2
	in if n<>0 then n
	  else exp_compare e1 e2
    | UnOp _, _ -> -1
    | _, UnOp _ -> 1
    | BinOp (o1,e1,f1), BinOp (o2,e2,f2) ->
	let n = binop_compare o1 o2
	in if n<>0 then n
	  else let n = exp_compare e1 e2
	    in if n<>0 then n
	      else exp_compare f1 f2
    | BinOp _, _ -> -1
    | _, BinOp _ -> 1
    | Lvar i1, Lvar i2 ->
	pvar_compare i1 i2
    | Lvar _, _ -> -1
    | _, Lvar _ -> 1
    | Fvar f1, Fvar f2 ->
        funname_compare f1 f2
    | Fvar _, _ -> -1
    | _, Fvar _ -> 1
    | Lfield (e1,f1), Lfield (e2,f2) ->
	let n = exp_compare e1 e2
	in if n<>0 then n
	  else fld_compare f1 f2
    | Lfield _, _ -> -1
    | _, Lfield _ -> 1
    | Lindex (e1,f1), Lindex (e2,f2) ->
	let n = exp_compare e1 e2
	in if n<>0 then n
	  else exp_compare f1 f2


let exp_equal e1 e2 = 
  exp_compare e1 e2 = 0

(** Compare atoms. Equalities come before disequalities *)
let atom_compare a b =
  if a==b then 0 else
    match (a,b) with
      | (Aeq (e1,e2), Aeq(f1,f2)) ->
	  let n = exp_compare e1 f1 in
	    if n<>0 then n else exp_compare e2 f2
      | (Aeq _, _) -> -1
      | (_, Aeq _) -> 1
      | (Aneq (e1,e2), Aneq (f1,f2)) ->
	  let n = exp_compare e1 f1 in
	    if n<>0 then n else exp_compare e2 f2
      | (Aneq _, _) -> -1
      | (_, Aneq _) -> 1
      | (Aless (e1,e2), Aless (f1,f2)) ->
	  let n = exp_compare e1 f1 in
	    if n<>0 then n else exp_compare e2 f2
      | (Aless _, _) -> -1
      | (_, Aless _) -> 1
      | (Aleq (e1,e2), Aleq(f1,f2)) ->
	  let n = exp_compare e1 f1 in
	    if n<>0 then n else exp_compare e2 f2


let atom_equal x y = atom_compare x y = 0

let rec strexp_compare se1 se2 =
  if se1==se2 then 0
  else match se1,se2 with
    | Eexp e1, Eexp e2 -> exp_compare e1 e2
    | Eexp _, _ -> -1
    | _, Eexp _ -> 1
    | Estruct fel1, Estruct fel2 -> fld_strexp_list_compare fel1 fel2
    | Estruct _, _ -> -1
    | _, Estruct _ -> 1
    | Earray (n1,esel1), Earray (n2,esel2) ->
	let n = int_compare n1 n2
	in if n<>0 then n
	  else exp_strexp_list_compare esel1 esel2

and fld_strexp_compare (fld1,se1) (fld2,se2) =
  let n = fld_compare fld1 fld2
  in if n<>0 then n
    else strexp_compare se1 se2

and fld_strexp_list_compare fel1 fel2 = match fel1,fel2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | fe1::l1, fe2::l2 ->
      let n = fld_strexp_compare fe1 fe2
      in if n<>0 then n
	else fld_strexp_list_compare l1 l2

and exp_strexp_compare (e1,se1) (e2,se2) =
  let n = exp_compare e1 e2
  in if n<>0 then n
    else strexp_compare se1 se2

and exp_strexp_list_compare esel1 esel2 = match esel1,esel2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | ese1::l1, ese2::l2 ->
      let n = exp_strexp_compare ese1 ese2
      in if n<>0 then n
	else exp_strexp_list_compare l1 l2

let strexp_equal se1 se2 = 
  (strexp_compare se1 se2 = 0)

let fld_strexp_equal fld_sexp1 fld_sexp2 = 
  (fld_strexp_compare fld_sexp1 fld_sexp2 = 0)

let exp_strexp_equal ese1 ese2 = 
  (exp_strexp_compare ese1 ese2 = 0)

let rec exp_list_compare el1 el2 = match el1,el2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | e1::l1, e2::l2 ->
      let n = exp_compare e1 e2
      in if n<>0 then n
	else exp_list_compare l1 l2


(** Comparsion between heap predicates. Hpointsto comes before others. *)
let rec hpred_compare hpred1 hpred2 =
  if hpred1==hpred2 then 0 else
    match (hpred1,hpred2) with
      | Hpointsto (e1,se1,t1), Hpointsto (e2,se2,t2) ->
	  let n = exp_compare e2 e1 in
	    if n<>0 then n else
	      let n = strexp_compare se2 se1 in
		if n<>0 then n else typ_compare t2 t1

let hpred_equal hpred1 hpred2 = 
  (hpred_compare hpred1 hpred2 = 0)


(** {2 Pretty Printing} *)
open Format

(** Pretty print an identifier. *)

(** Print a sequence. *)
let rec pp_seq pp f = function
  | [] -> ()
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a,%a" pp x (pp_seq pp) l

(** Pretty print a unary operator. *)
let str_unop = function
  | Cil.Neg -> "-"
  | Cil.BNot -> "~"
  | Cil.LNot -> "!"

(** Pretty print a binary operator. *)
let str_binop = function
  | Cil.PlusA -> "+"
  | Cil.PlusPI -> "+pi+"
  | Cil.IndexPI -> "+ipi+"
  | Cil.MinusA -> "-"
  | Cil.MinusPI -> "-pi-"
  | Cil.MinusPP -> "-pp-"
  | Cil.Mult -> "*"
  | Cil.Div -> "/"
  | Cil.Mod -> "%"
  | Cil.Shiftlt -> "<<"
  | Cil.Shiftrt -> ">>"
  | Cil.Lt -> "<"
  | Cil.Gt -> ">"
  | Cil.Le -> "<="
  | Cil.Ge -> ">="
  | Cil.Eq -> "=="
  | Cil.Ne -> "!="
  | Cil.BAnd -> "&"
  | Cil.BXor -> "^"
  | Cil.BOr -> "|"
  | Cil.LAnd -> "&&"
  | Cil.LOr -> "||"

(** Pretty print a type. *)
let rec pp_typ f _ = ()
(*
function 
  | Tvar tname -> fprintf f "%a" pp_name tname
  | Tint -> fprintf f "int"
  | Tvoid -> fprintf f "void" 
  | Tfun -> fprintf f "_function_"
  | Tptr typ -> fprintf f "%a*" pp_typ typ
  | Tstruct ftl -> 
      fprintf f "struct {%a}"
      (pp_seq (fun f (fld,t) -> fprintf f "%a %a" pp_typ t pp_name fld)) ftl
  | Tarray (typ,n) -> fprintf f "%a[%d]" pp_typ typ n
*)

let pp_pair f ((fld:fieldname),(t:typ)) =
  fprintf f "%a %a" pp_typ t pp_name fld


(** Pretty print an expression. *)
let rec pp_exp f = function
  | Var id -> pp_ident f id
  | Const_int n -> fprintf f "%d" n
  | Cast (typ,e) -> fprintf f "(%a)%a" pp_typ typ pp_exp e
  | UnOp (op,e) -> fprintf f "%s%a" (str_unop op) pp_exp e
  | BinOp (op,e1,e2) -> fprintf f "(%a%s%a)" pp_exp e1 (str_binop op) pp_exp e2
  | Lvar pv -> fprintf f "&%a" pp_name pv.pv_name
  | Fvar fn -> fprintf f "%a" pp_name fn
  | Lfield (e,fld) -> fprintf f "%a.%a" pp_exp e pp_name fld
  | Lindex (e1,e2) -> fprintf f "%a[%a]" pp_exp e1 pp_exp e2

(** Pretty print a location *)
let pp_loc f (loc:Cil.location) =
  fprintf f "[line %d]" loc.Cil.line

let pp_exp_typ f (e,t) =
  fprintf f "%a:%a" pp_exp e pp_typ t

(** Pretty print an instruction. *)
let pp_instr f = function
  | Letderef (id,e,t,loc) -> fprintf f "%a=*%a:%a %a" pp_ident id pp_exp e pp_typ t pp_loc loc
  | Set (e1,t,e2,loc) -> fprintf f "*%a:%a=%a %a" pp_exp e1 pp_typ t pp_exp e2 pp_loc loc
  | Call (eto,e,arg_ts,loc) ->
      (match eto with
	| None -> ()
	| Some (e1,t1,root_t) -> fprintf f "*%a=(%a)" pp_exp e1 pp_typ t1);
      fprintf f "%a(%a) %a" pp_exp e (pp_seq pp_exp_typ) arg_ts pp_loc loc

let rec pp_instr_list f = function
  | [] -> fprintf f "@."
  | i::is -> fprintf f "  %a;@.%a" pp_instr i pp_instr_list is

let pp_atom f = function
  | Aeq (e1,e2) -> fprintf f "%a=%a" pp_exp e1 pp_exp e2
  | Aneq (e1,e2) -> fprintf f "%a!=%a" pp_exp e1 pp_exp e2
  | Aless (e1,e2) -> fprintf f "%a<%a" pp_exp e1 pp_exp e2
  | Aleq (e1,e2) -> fprintf f "%a<=%a" pp_exp e1 pp_exp e2



let rec pp_sexp f = function
  | Eexp e -> pp_exp f e
  | Estruct fel ->
      fprintf f "{%a}" (pp_seq (fun f (n,se) -> fprintf f "%a:%a" pp_name n pp_sexp se)) fel
  | Earray (size,nel) ->
      fprintf f "[%a]" (pp_seq (fun f (i,se) -> fprintf f "%a:%a" pp_exp i pp_sexp se)) nel

(** Print a *-separated sequence. *)
let rec pp_star_seq pp f = function
  | [] -> ()
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a * %a" pp x (pp_star_seq pp) l


let rec pp_hpred f = function
  | Hpointsto (e,se,t) -> fprintf f "%a|->%a:%a" pp_exp e pp_sexp se pp_typ t


let rec pp_hpred_list f = function
  | [] -> ()
  | [hp] -> 
      Format.fprintf f "%a" pp_hpred hp
  | hp::hps -> 
      Format.fprintf f "%a * %a" pp_hpred hp pp_hpred_list hps




(** {2 Functions for computing program variables} *)

let rec exp_fpv = function 
  | Var id -> []
  | Const_int n -> []
  | Cast (_, e) | UnOp (_, e) -> exp_fpv e
  | BinOp (_, e1, e2) -> exp_fpv e1 @ exp_fpv e2 
  | Lvar name -> [name] 
  | Fvar _ -> []
  | Lfield (e, _) -> exp_fpv e
  | Lindex (e1, e2) -> exp_fpv e1 @ exp_fpv e2

let rec strexp_fpv = function
  | Eexp e -> exp_fpv e
  | Estruct fld_se_list -> 
      let f (_,se) = strexp_fpv se
      in List.flatten (List.map f fld_se_list)
  | Earray (size, idx_se_list) ->
      let f (idx,se) = exp_fpv idx @ strexp_fpv se
      in List.flatten (List.map f idx_se_list)

let atom_fpv = function
  | Aeq (e1,e2) | Aneq (e1,e2) 
  | Aless (e1,e2) | Aleq (e1,e2) -> exp_fpv e1 @ exp_fpv e2


let rec hpred_fpv = function
  | Hpointsto (base, se, _) -> 
      exp_fpv base @ strexp_fpv se

(** {2 Functions for computing free non-program variables} *)

(** Type of free variables. These include primed, normal and footprint variables. We keep a count of how many types the variables appear. *)
type fav = ident list ref

let fav_new () =
  ref []

(** Emptyness check. *)
let fav_is_empty fav = match !fav with
  | [] -> true
  | _ -> false

(** extend [fav] with a [id] *)
let (++) fav id =
  fav := id::!fav

(** extend [fav] with ident list [idl] *)
let (+++) fav idl =
  List.iter (fun id -> fav ++ id) idl

(** Convert a list to a fav. *)
let fav_from_list l =
  let fav = fav_new () in
  let _ = List.iter (fun id -> fav ++ id) l
  in fav

let rec remove_duplicates_from_sorted special_equal = function
  | [] -> []
  | [x] -> [x]
  | x::y::l -> 
      if (special_equal x y) 
      then remove_duplicates_from_sorted special_equal (y::l)
      else x::(remove_duplicates_from_sorted special_equal (y::l))

(** Convert a [fav] to a list of identifiers without repetitions. *)
let fav_to_list fav =
  remove_duplicates_from_sorted ident_equal (List.sort ident_compare !fav)

(** Pretty print a fav. *)
let pp_fav f fav =
  (pp_seq pp_ident) f (fav_to_list fav)

(** Copy a [fav]. *)
let fav_copy fav =
  ref (List.map (fun x -> x) !fav)

(** Turn a xxx_fav_add function into a xxx_fav function *)
let fav_imperative_to_functional f x =
  let fav = fav_new () in
  let _ = f fav x
  in fav

(** [fav_filter_ident fav f] only keeps [id] if [f id] is true. *)
let fav_filter_ident fav filter =
  fav := List.filter filter !fav

(** Like [fav_filter_ident] but return a copy. *)
let fav_copy_filter_ident fav filter =
  ref (List.filter filter !fav)

(** checks whether every element in l1 appears l2 **)
let rec ident_sorted_list_subset l1 l2 =
  match l1,l2 with
    | [],_ -> true
    | _::_,[] -> false
    | id1::l1, id2::l2 ->
	let n = ident_compare id1 id2 in
	  if n=0 then ident_sorted_list_subset l1 (id2::l2)
	  else if n>0 then ident_sorted_list_subset (id1::l1) l2
	  else false


(** [fav_subset_ident fav1 fav2] returns true if every ident in [fav1]
    is in [fav2].*)
let fav_subset_ident fav1 fav2 =
  ident_sorted_list_subset (fav_to_list fav1) (fav_to_list fav2)

let fav_mem fav id =
  List.mem id !fav

let rec exp_fav_add fav = function 
  | Var id -> fav ++ id
  | Const_int n -> ()
  | Cast (_, e) | UnOp (_, e) -> exp_fav_add fav e
  | BinOp (_, e1, e2) -> exp_fav_add fav e1; exp_fav_add fav e2 
  | Lvar id -> () (* do nothing since we only count non-program variables *)
  | Fvar fn -> () (* we do not count function names, either *)
  | Lfield (e, _) -> exp_fav_add fav e
  | Lindex (e1, e2) -> exp_fav_add fav e1; exp_fav_add fav e2

let exp_fav =
  fav_imperative_to_functional exp_fav_add

let rec ident_in_exp id e =
  let fav = fav_new () in 
  let _ = exp_fav_add fav e 
  in fav_mem fav id

let rec strexp_fav_add fav = function
  | Eexp e -> exp_fav_add fav e
  | Estruct fld_se_list ->
      List.iter (fun (_,se) -> strexp_fav_add fav se) fld_se_list
  | Earray (_, idx_se_list) ->
      List.iter (fun (e,se) -> exp_fav_add fav e; strexp_fav_add fav se) idx_se_list

let atom_fav_add fav = function
  | Aeq (e1,e2) | Aneq(e1,e2) | Aless(e1,e2) | Aleq(e1,e2)
      -> exp_fav_add fav e1; exp_fav_add fav e2

let atom_fav =
  fav_imperative_to_functional atom_fav_add

let rec hpred_fav_add fav = function
  | Hpointsto (base, sexp, t) -> exp_fav_add fav base; strexp_fav_add fav sexp

(** {2 Functions for Substitution} *)

(** substitution *)
type subst = (ident * exp) list

(** Create a substitution from a list of pairs. *)
let sub_of_list sub =
  sub

(** Convert a subst to a list of pairs. *)
let sub_to_list sub =
  sub

(** The empty substitution. *)
let sub_empty = sub_of_list []

(** Comparison between substitutions. *) 
let rec sub_compare (sub1:subst) (sub2:subst) =
  if sub1==sub2 then 0
  else match (sub1,sub2) with
    | ([],[]) -> 0
    | ([],_::_) -> -1
    | ((i1,e1)::sub1',(i2,e2)::sub2') ->
	let n = ident_compare i1 i2
	in if n<>0 then n
	  else let n = exp_compare e1 e2
	    in if n<>0 then n
	      else sub_compare sub1' sub2'
    | (_::_,[]) -> 1

(** Equality for substitutions. *) 
let sub_equal sub1 sub2 =
  sub_compare sub1 sub2 = 0

(** Join two substitutions into one. *)
(** Hongseok: Dangerous operation. Might break the invariant that no substitutions give
    two definitions of an identifier. *)
let sub_join = (@)

(** [sub_find filter sub] returns the expression associated to the first identifier that satisfies [filter]. Raise [Not_found] if there isn't one. *)
let sub_find filter (sub:subst) =
  snd (List.find (fun (i,_) -> filter i) sub)

(** [sub_filter filter sub] restricts the domain of [sub] to the
    identifiers satisfying [filter]. *)
let sub_filter filter (sub:subst) =
  List.filter (fun (i,_) -> filter i) sub

(** [sub_range_partition filter sub] partitions [sub] according to
    whether range expressions satisfy [filter]. *)
let sub_range_partition filter (sub:subst) =
  List.partition (fun (_,e) -> filter e) sub

(** [sub_domain_partition filter sub] partitions [sub] according to
    whether domain identifiers satisfy [filter]. *)
let sub_domain_partition filter (sub:subst) =
  List.partition (fun (i,_) -> filter i) sub

(** Return the list of expressions in the range of the substitution. *)
let sub_range sub =
  List.map snd sub

(** [sub_range_map f sub] applies [f] to the expressions in the range of [sub]. *)
let sub_range_map f sub =
  List.map (fun (i,e) -> (i, f e)) sub

let mem_sub id sub =
  List.exists (fun (id1,_) -> ident_equal id id1) sub

(** Extend substitution and return [None] if not possible. *)
let extend_sub sub id exp : subst option = 
 if mem_sub id sub then None else Some ((id,exp)::sub)

(** Free auxilary variables in the domain and range of the
    substitution. *)
let sub_fav_add fav (sub:subst) =
  List.iter (fun (id,e) -> fav++id; exp_fav_add fav e) sub

(** Substitutions do not contain binders *)
let sub_av_add = sub_fav_add

let rec exp_sub (subst:subst) e = match e with
  | Var id ->
      let rec apply_sub = function
	| [] -> e
	| (i,e)::l -> if ident_equal i id then e else apply_sub l
      in apply_sub subst
  | Const_int n -> 
      Const_int n
  | Cast (t,e1) -> 
      let e1' = exp_sub subst e1 
      in Cast (t,e1')
  | UnOp (op, e1) ->
      let e1' = exp_sub subst e1
      in UnOp(op, e1')
  | BinOp (op, e1, e2) ->
      let e1' = exp_sub subst e1 in
      let e2' = exp_sub subst e2 
      in BinOp (op, e1', e2')
  | Lvar _ | Fvar _ ->
      e
  | Lfield (e1,fld) ->
      let e1' = exp_sub subst e1 
      in Lfield (e1',fld)
  | Lindex (e1,e2) ->
      let e1' = exp_sub subst e1 in
      let e2' = exp_sub subst e2 
      in Lindex (e1',e2')

let rec strexp_sub (subst:subst) = function
  | Eexp e -> Eexp (exp_sub subst e)
  | Estruct fld_cnt_list ->
      let f (fld,cnt) = (fld, strexp_sub subst cnt) in
      let fld_cnt_list' = List.map f fld_cnt_list 
      in Estruct fld_cnt_list'
  | Earray (size, idx_cnt_list) ->
      let f (idx,cnt) = (exp_sub subst idx, strexp_sub subst cnt) in
      let idx_cnt_list' = List.map f idx_cnt_list
      in Earray (size, idx_cnt_list')

let atom_sub subst = function
  | Aeq (e1, e2) -> 
      let e1' = exp_sub subst e1 in
      let e2' = exp_sub subst e2 
      in Aeq (e1', e2') 
  | Aneq (e1, e2) ->
      let e1' = exp_sub subst e1 in
      let e2' = exp_sub subst e2 
      in Aneq (e1', e2')
  | Aless (e1, e2) ->
      let e1' = exp_sub subst e1 in
      let e2' = exp_sub subst e2 
      in Aless (e1', e2')
  | Aleq (e1, e2) ->
      let e1' = exp_sub subst e1 in
      let e2' = exp_sub subst e2 
      in Aleq (e1', e2')

let rec hpred_sub (subst:subst)  = function
  | Hpointsto (lval, cnt, t) ->
      let lval' = exp_sub subst lval in
      let cnt' = strexp_sub subst cnt 
      in Hpointsto (lval',cnt',t)

(** {2 Type Environment} *)
(** has tables on strings *)

(** Type for type environment. *)
type tenv = typ NameHash.t

(** Global type environment. *)
let tenv = NameHash.create 1000

(** Look up a name in the global type environment. *) 
let tenv_lookup name =
  try Some (NameHash.find tenv name)
  with Not_found -> None

(** Add a (name,type) pair to the global type environment. *)
let tenv_add name typ =
  NameHash.add tenv name typ;
  Error.log "  Extending tyenv with %a: %a@." pp_name name pp_typ typ

(** {2 Functions for constructing or destructing entities in this module} *)

let mk_pvar (name:name) (fundec:Cil.fundec) : pvar =
  let funname = fundec.Cil.svar.Cil.vname in
  let funid = fundec_to_int fundec
  in {pv_name = name; pv_funid = funid; pv_funname = funname}

(** Compute the offset list of an expression *)
let exp_get_offsets exp = 
  let rec f offlist_past e = match e with
    | Var _ | Const_int _ | UnOp _ | BinOp _ | Lvar _ | Fvar _ -> offlist_past
    | Cast(t,sub_exp) -> f offlist_past sub_exp
    | Lfield(sub_exp,fldname) -> f (Off_fld(fldname)::offlist_past) sub_exp
    | Lindex(sub_exp,e) -> f (Off_index(e)::offlist_past) sub_exp
  in f [] exp

