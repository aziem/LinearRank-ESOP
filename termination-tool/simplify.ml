open Ident
open Sil
open Prop
open Format
open Printf

module E = Error

let unop_to_string op = match op with 
  | Cil.Neg -> "- "
  | Cil.BNot -> assert false
  | Cil.LNot -> assert false

let binop_to_string op = match op with 
  | Cil.PlusA -> " + "
  | Cil.MinusA -> " - "
  | Cil.Mult -> " * "
  | Cil.Div -> assert false (* Simplify doesnt like / *)
  | _ -> assert false

let rec exp_to_string e = match e with 
  | Var id -> ident_to_rankfinder_string id
  | Const_int n -> string_of_int n
  | Cast(typ,e1) -> exp_to_string e1
  | UnOp(op,e1) -> "(" ^ (unop_to_string op) ^ (exp_to_string e1) ^ ")" 
  | BinOp(op,e1,e2) -> 
      let s1 = exp_to_string e1 in 
      let s2 = exp_to_string e2 in 
      let s3 = binop_to_string op 
      in "(" ^ s3 ^ s1 ^ s2 ^ ")"
  | Lvar _ 
  | Fvar _ 
  | Lfield _
  | Lindex _ -> assert false

let atom_to_string a = match a with 
  | Aeq(e1,e2) -> "(EQ " ^ (exp_to_string e1) ^  (exp_to_string e2) ^ ")"
  | Aneq(e1,e2) ->"(NEQ " ^  (exp_to_string e1) ^  (exp_to_string e2) ^ ")"
  | Aless(e1,e2) -> "(< " ^ (exp_to_string e1) ^ (exp_to_string e2) ^ ")"
  | Aleq(e1,e2) -> "(<= " ^ (exp_to_string e1) ^ (exp_to_string e2) ^ ")"

(* string to register the atoms in simplify *)
let rec atom_list_to_string = function
  | [] -> ""
  | [se] -> atom_to_string se
  | se::se_list -> "(BG_PUSH(" ^(atom_to_string se) ^ ") " ^ (atom_list_to_string se_list) 

(* add the goal FALSE to the end of the simplify premises *)
let _pure_to_simplify pi = 
	(atom_list_to_string pi) ^ " FALSE" 

let simplify_buffer = String.create 1000

let _simplify_run str = 
	let oc = open_out "simplify.in" in 
	Printf.fprintf oc "%s" str;
	ignore (Unix.close_process_out oc);
	(* -nosc means only answer is printed rather than counterexample + ans *)
	let ic = Unix.open_process_in (!Config.simplify_file ^ " -nosc simplify.in")
	in 
	let size_in = input ic simplify_buffer 0 1000 in 
	let str_in = String.sub simplify_buffer 0 size_in in 
	let validregexp = Str.regexp "Valid" in 
	try 
		ignore(Unix.close_process_in ic); 
		ignore (Str.search_forward validregexp str_in 0);
		true
	with 
		| Not_found -> false

let simplify prop = 
	E.log "@[<2>....CALLING SIMPLIFY....@\n";
	let pi = prop_get_pi prop in 
	let b = _simplify_run (_pure_to_simplify pi) in
	if b then (E.log "INCONS@\n@.") else (E.log "CONSISTENT@\n@.");b

	
	
