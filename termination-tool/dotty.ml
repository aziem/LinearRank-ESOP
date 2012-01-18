open Pretty
open Cil
module E = Errormsg

(* Most of this has been ripped from cil.ml *)

(* exp to string functions *)

let error_sids : int list ref = ref []

let s_unop () u =
  match u with
    Neg -> "-"
  | BNot -> "~"
  | LNot -> "!"

let s_binop () b =
  match b with
    PlusA | PlusPI | IndexPI -> "+"
  | MinusA | MinusPP | MinusPI -> "-"
  | Mult -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Shiftrt-> ">>"
  | Shiftlt-> "<<"
  | Lt -> "<"
  | Gt -> ">"
  | Le -> "<="
  | Ge -> ">="
  | Eq -> "=="
  | Ne -> "!="
  | BAnd -> "&"
  | BXor -> "^"
  | BOr -> "|"
  | LAnd -> "&&"
  | LOr -> "||"


let s_const () c = 
  match c with
     CInt64(_, _, Some s) -> s (* Always print the text if there is one *)
   | CInt64(i, ik, None) -> Int64.to_string i
  (*    (** We must make sure to capture the type of the constant. For some 
       * constants this is done with a suffix, for others with a cast prefix.*)
      let suffix : string = 
        match ik with
          IUInt -> "U"
        | ILong -> "L"
        | IULong -> "UL"
        | ILongLong -> rmsvcMode then "L" else "LL"
        | IULongLong -> if !msvcMode then "UL" else "ULL"
        | _ -> ""
      in
      let prefix : string = 
        if suffix <> "" then "" 
        else if ik = IInt then ""
        else "(" ^ (sprint !lineLength (d_ikind () ik)) ^ ")"
      in
      (* Watch out here for negative integers that we should be printing as 
       * large positive ones *)
      if i < Int64.zero 
          && (match ik with 
            IUInt | IULong | IULongLong | IUChar | IUShort -> true | _ -> false) then
        let high = Int64.shift_right i 32 in
        if ik <> IULongLong && ik <> ILongLong && high = Int64.of_int (-1) then
          (* Print only the low order 32 bits *)
          (prefix ^ "0x" ^ 
                (Int64.format "%x" 
                  (Int64.logand i (Int64.shift_right_logical high 32))
                ^ suffix))
        else
          (prefix ^ "0x" ^ Int64.format "%x" i ^ suffix)
      else (
        if (i = mostNeg32BitInt) then
          (* sm: quirk here: if you print -2147483648 then this is two tokens *)
          (* in C, and the second one is too large to represent in a signed *)
          (* int.. so we do what's done in limits.h, and print (-2147483467-1); *)
          (* in gcc this avoids a warning, but it might avoid a real problem *)
          (* on another compiler or a 64-bit architecture *)
          (prefix ^ "(-0x7FFFFFFF-1)")
        else if (i = mostNeg64BitInt) then
          (* The same is true of the largest 64-bit negative. *)
          (prefix ^ "(-0x7FFFFFFFFFFFFFFF-1)")
        else
          (prefix ^ (Int64.to_string i ^ suffix))
      )
*)
  | CStr(s) -> ("\"" ^ s ^ "\"")
  | CWStr(s) -> "Not done yet"
      (* text ("L\"" ^ escape_string s ^ "\"")  *)
      (*(List.fold_left (fun acc elt -> 
        acc ++ 
        if (elt >= Int64.zero &&
            elt <= (Int64.of_int 255)) then 
          ((Char.chr (Int64.to_int elt)))
        else
          ((Printf.sprintf "\\x%LX\"" elt) ++ break ++
            ("\""))
      ) ("L\"") s ) ++ text "\""*)
      (* we cannot print L"\xabcd" "feedme" as L"\xabcdfeedme" --
       * the former has 7 wide characters and the later has 3. *)

  | CChr(c) -> (*("'" ^ c ^ "'")*) "Not done yet"
  | CReal(_, _, Some s) -> s
  | CReal(f, _, None) -> (string_of_float f)
  | CEnum(_, s, ei) -> s

let s_lval () (l,o) = 
	match l with 
	| Var(v) -> v.vname
	| _ -> "Not done yet"	

let rec s_exp () e = 
	match e with 
	| Const(c) -> s_const () c
	| Lval(l) -> s_lval () l
	| UnOp(u,e1,_) -> (s_unop () u) ^ " " ^ (s_exp () e1) 
	| BinOp(b,e1,e2,_) -> (s_exp () e1) ^ " " ^ (s_binop () b) ^ " " ^ (s_exp () e2)
	| _ -> "Not done yet"

let rec forallStmts (todo) (fd : fundec) = 
  begin
    fasBlock todo fd.sbody;
  end

and fasBlock (todo) (b : block) =
  List.iter (fasStmt todo) b.bstmts

and fasStmt (todo) (s : stmt) =
  begin
    ignore(todo s);
    match s.skind with
      | Block b -> fasBlock todo b
      | If (_, tb, fb, _) -> (fasBlock todo tb; fasBlock todo fb)
      | Switch (_, b, _, _) -> fasBlock todo b
      | Loop (b, _, _, _) -> fasBlock todo b
      | (Return _ | Break _ | Continue _ | Goto _ | Instr _) -> ()
      | TryExcept _ | TryFinally _ -> E.s (E.unimp "try/except/finally")
  end
;;

let instrs_to_string i = 
        let var_to_string var = match var with
                | Var(v) -> v.vname 
                | _ -> ""
        in 
        let rec _instrs_to_string i =
                match i with
                | [] -> ""
                | Set((l,o) ,e,loc) :: tl -> (var_to_string l) ^ " = " ^  (s_exp () e) ^ "\\n" ^ (_instrs_to_string tl)  
                | Call(Some((l,o)),e,el,loc) :: tl -> (var_to_string l) ^ "=" ^ (s_exp () e) ^ "\\n"  ^ (_instrs_to_string tl) 
								| _ :: tl -> "" ^ _instrs_to_string tl
        in
        _instrs_to_string i

        

let d_cfgnodename () (s : stmt) =
  dprintf "%d" s.sid

let d_cfgnodelabel () (s : stmt) =
  let label = 
  begin
    match s.skind with
      | If (e, _, _, _)  -> "if (" ^ (s_exp () e) ^ ")" 
      | Loop _ -> "loop"
      | Break _ -> "break"
      | Continue _ -> "continue"
      | Goto _ -> "goto"
      | Instr(il) -> instrs_to_string il
      | Switch _ -> "switch"
      | Block _ -> "block"
      | Return _ -> "return"
      | TryExcept _ -> "try-except"
      | TryFinally _ -> "try-finally"
  end in
    dprintf "%d: %s" s.sid label

let d_cfgedge (src) () (dest) =
  	if (List.mem src.sid !error_sids) && (List.mem dest.sid !error_sids) then 
			begin
			dprintf "%a -> %a [color=red]"
    	d_cfgnodename src
    	d_cfgnodename dest
			end
		else
			begin
			dprintf "%a -> %a"
    	d_cfgnodename src
    	d_cfgnodename dest
			end
		
let d_cfgnode () (s : stmt) =
		if (List.mem s.sid !error_sids ) then 
			begin 
    	dprintf "%a [color=red,label=\"%a\"]\n\t%a" 
    	d_cfgnodename s
    	d_cfgnodelabel s
    	(d_list "\n\t" (d_cfgedge s)) s.succs
			end
		else 
			begin
    	dprintf "%a [label=\"%a\"]\n\t%a" 
    	d_cfgnodename s
    	d_cfgnodelabel s
    	(d_list "\n\t" (d_cfgedge s)) s.succs
			end

(**********************************************************************)
(* entry points *)

(** print control flow graph (in dot form) for fundec to channel *)
let printCfgChannel (chan : out_channel) (fd : fundec) =
  let pnode (s:stmt) = fprintf chan "%a\n" d_cfgnode s in
    begin
      ignore (fprintf chan "digraph CFG_%s {\n" fd.svar.vname);
      forallStmts pnode fd;
      ignore(fprintf chan  "}\n");
    end

(** Print control flow graph (in dot form) for fundec to file *)
let printCfgFilename (filename : string) (fd : fundec) (bad_sid : int list) =
  error_sids := bad_sid;
  let chan = open_out filename in
    begin
      printCfgChannel chan fd;
      close_out chan;
			error_sids := []
    end


