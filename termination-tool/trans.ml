open Cil

(** list of instructions to translate impure expressions, and the list
    of local variables generated *)
type temp_list = Ident.ident list * Sil.instr list

let mk_ext e = (([],[]),e)

let name_siltmp = Ident.string_to_name "siltmp"

(** Translation of a cil type into a sil type **)
let rec trans_typ (handled_names : Ident.name list) (t : typ) : Sil.typ =
  match t with
    | TVoid _ -> Sil.Tvoid
    | TInt _ -> Sil.Tint
    | TFloat _ -> assert false
    | TPtr (t,_) -> Sil.Tptr(trans_typ handled_names t)
    | TArray (t,eo,_) ->
	(match eo with
	  | Some (Const (CInt64 (n,_,_))) -> 
              Sil.Tarray(trans_typ handled_names t, Int64.to_int n)
	  | _ ->
	      assert false)
    | TFun _ -> Sil.Tfun
    | TNamed (ti,_) -> trans_typeinfo handled_names ti
    | TComp (ci,_) -> trans_compinfo handled_names ci
    | TEnum _ -> Sil.Tint
    | TBuiltin_va_list _ -> 
	assert false

and trans_typeinfo (handled_names : Ident.name list) (ti : typeinfo) : Sil.typ =
  let name = Ident.string_to_name ti.tname in
    match Sil.tenv_lookup name with
      | Some t -> t
      | None ->
	  let t = trans_typ handled_names ti.ttype
	  in Sil.tenv_add name t;
	    t

and trans_compinfo (handled_names : Ident.name list) (ci : compinfo) : Sil.typ =
  let fields = ci.cfields in
  let name = Ident.string_to_name ci.cname in
    if (List.mem name handled_names) then Sil.Tvar name else
      match Sil.tenv_lookup name with
	| Some t -> t
	| None ->
            let handled_names' = name::handled_names in
            let trans_field fi = (Ident.string_to_name fi.fname, trans_typ handled_names' fi.ftype) in
	    let t = Sil.Tstruct (List.map trans_field fields) 
            in Sil.tenv_add name t; 
              t

(** Return the root of an lval *)
let rec root_of_lval lval =
  let (lval',offset) = removeOffsetLval lval
  in if offset=NoOffset then lval'
    else root_of_lval lval'

(** Return the Sil type of the root of an lval *)
let sil_type_of_lval_root lval =
  let lval = root_of_lval lval in
  let cil_t = typeOfLval lval
  in trans_typ [] cil_t

(** Translation of an expression into a sequence of sil instructions **)
let rec trans_exp (fundec:fundec) (e : exp) : temp_list * Sil.exp =
  match e with
    | Const(CInt64(n,_,_)) -> mk_ext (Sil.Const_int (Int64.to_int(n)))
    | Const _ -> mk_ext (Sil.Const_int (-7777))
    | Lval lval ->  (** note: it's a dereference *)
	let ((idl,stmtl),e) = trans_lval fundec lval in
        let id = Ident.create_fresh_normal_ident name_siltmp in
        let sil_t = sil_type_of_lval_root lval in
	let stmt = Sil.Letderef (id,e,sil_t,Cil.locUnknown)
        in ((idl@[id],stmtl@[stmt]),Sil.Var id)
    | SizeOf _ -> mk_ext (Sil.Const_int (-8888))
    | SizeOfE _ -> assert false
    | SizeOfStr _ -> assert false
    | AlignOf _ -> assert false
    | AlignOfE _ -> assert false
    | UnOp (op,e,_) ->
	let ((idl1,stml1),e1) = trans_exp fundec e
	in ((idl1,stml1),Sil.UnOp(op,e1))
    | BinOp (op,e1,e2,_) ->
	let ((idl1,stml1),e1) = trans_exp fundec e1 in
	let ((idl2,stml2),e2) = trans_exp fundec e2
	in ((idl1@idl2,stml1@stml2),Sil.BinOp(op,e1,e2))
    | CastE (t,e) -> 
(*      let t' = trans_typ [] t in *)
	let ((idl,stml),e') = trans_exp fundec e
	in (* ((idl,stml),Sil.Cast (t',e')) *)
          ((idl,stml), e')
    | AddrOf lval -> trans_lval fundec lval
    | StartOf lval -> trans_lval fundec lval

and trans_lval (fundec:fundec) ((lhost,off) : lval) : temp_list * Sil.exp =
  let ((idl1,stml1),e1) = trans_lhost fundec lhost in
  let ((idl2,stml2),e2) = trans_offset fundec e1 off
  in ((idl1@idl2,stml1@stml2),e2)

and trans_lhost (fundec:fundec) (lhost:lhost) : temp_list * Sil.exp =
  match lhost with
    | Var vinfo ->
	let name = Ident.string_to_name vinfo.vname
	in mk_ext (Sil.Lvar (Sil.mk_pvar name fundec))
    | Mem e -> trans_exp fundec e

and trans_offset (fundec:fundec) (e:Sil.exp) (off:offset) : temp_list * Sil.exp =
  match off with
    | NoOffset -> mk_ext e
    | Field (fi,off') ->
	let e' = Sil.Lfield (e,Ident.string_to_name fi.fname)
	in trans_offset fundec e' off'
    | Index (e',off') ->
	let ((idl1,stml1),e1) = trans_exp fundec e' in
	let ((idl2,stml2),e2) = trans_offset fundec (Sil.Lindex (e,e1)) off'
	in ((idl1@idl2,stml1@stml2),e2)

let trans_explist (fundec:fundec) el =
  let lst = List.map (trans_exp fundec) el in   
  let f ((idl,stmtl),e) ((idl',stmtl'),elist) = ((idl@idl', stmtl@stmtl'), e::elist)
  in List.fold_right f lst (([],[]),[])

(** Translation of an expression into a sequence of sil instructions *)
let rec trans_instr (fundec:fundec) (instr : instr) : temp_list =
  match instr with
    | Set (lval,e,_) ->
	let ((idl1,stmtl1),e1) = trans_lval fundec lval in
	let ((idl2,stmtl2),e2) = trans_exp fundec e in
        let sil_t = sil_type_of_lval_root lval in
	let stmt = Sil.Set (e1,sil_t,e2,get_instrLoc instr)
	in (idl1@idl2,stmtl1@stmtl2@[stmt])
    | Call (lvalo,e,args,_) ->
	let ((idl1,stmtl1),eto) = match lvalo with
	  | None -> (([],[]),None)
	  | Some lval ->
	      let ((idl1,stmt1),sil_e) = trans_lval fundec lval in
              let cil_t = typeOfLval lval in
              let sil_t = trans_typ [] cil_t in
	      let sil_root_t = sil_type_of_lval_root lval
	      in ((idl1,stmt1),Some (sil_e,sil_t,sil_root_t)) in
	let ((idl2,stmtl2),e2) = match e with
          | Lval (Var vi, NoOffset) ->  (* call without function pointers *)
	      let name = Ident.string_to_name vi.vname 
	      in mk_ext (Sil.Fvar name)		   
 	  | _ -> trans_exp fundec e in
        let ((idl3,stmtl3),args3) = trans_explist fundec args in
        let ts3 = List.map (fun e -> trans_typ [] (typeOf e)) args in
        let arg_ts3 = try List.combine args3 ts3 with Invalid_argument _ -> assert false in 
	let stmt = Sil.Call(eto,e2,arg_ts3,get_instrLoc instr)
	in (idl1@idl2@idl3,stmtl1@stmtl2@stmtl3@[stmt])
(*
    | Call (lvalo,e,_,_) ->
	let ((idl1,stmtl1),eo) = match lvalo with
	  | None -> (([],[]),None)
	  | Some lval ->
	      let ((idl1,stmt1),e') = trans_lval lval
	      in ((idl1,stmt1),Some e') in
	let ((idl2,stmtl2),e1) = trans_exp e in
	let stmt = Sil.Call(eo,e1)
	in (idl1@idl2,stmtl1@stmtl2@[stmt])
*)
    | Asm _ -> assert false (** are you kidding? *)
