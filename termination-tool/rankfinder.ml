open Sil
open Ident
open Format
open Prop

module E = Error

let unop_to_string op = match op with 
  | Cil.Neg -> "-"
  | Cil.BNot -> assert false
  | Cil.LNot -> assert false

let binop_to_string op = match op with 
  | Cil.PlusA -> " + "
  | Cil.MinusA -> " - "
  | Cil.Mult -> " * "
  | Cil.Div -> " / "
  | _ -> assert false

let rec remove_double_minus e = match e with
  | Var _ | Const_int _ -> 
      e
  | Cast(typ,e1) -> 
      Cast(typ, remove_double_minus e1)
  | UnOp(Cil.Neg,(UnOp(Cil.Neg,e1))) -> 
      remove_double_minus e1
  | UnOp(op,e1) -> 
      UnOp(op,remove_double_minus e1) 
  | BinOp(op,e1,e2) -> 
      let e1' = remove_double_minus e1 in 
      let e2' = remove_double_minus e2 
      in BinOp(op,e1',e2')
  | Lvar _ | Fvar _ ->
      e
  | Lfield (e1,fname) ->
      let e1' = remove_double_minus e1 
      in Lfield(e1',fname)
  | Lindex (e1,e2) ->
      let e1' = remove_double_minus e1 in
      let e2' = remove_double_minus e2 
      in Lindex (e1',e2') 

let rec _exp_to_string e = match e with 
  | Var id -> ident_to_rankfinder_string id
  | Const_int n -> string_of_int n
  | Cast(typ,e1) -> _exp_to_string e1
  | UnOp(op,e1) -> "(" ^ (unop_to_string op) ^ (_exp_to_string e1) ^ ")"
  | BinOp(op,e1,e2) -> 
      let s1 = _exp_to_string e1 in 
      let s2 = _exp_to_string e2 in 
      let s3 = binop_to_string op 
      in "(" ^ s1 ^ s3 ^  s2 ^ ")"
  | Lvar _ 
  | Fvar _ 
  | Lfield _
  | Lindex _ -> assert false

let exp_to_string p e = _exp_to_string e

let rec exp_list_to_string p = function
  | [] -> ""
  | [e] -> exp_to_string p e
  | e::e_list -> (exp_to_string p e) ^ ", " ^ (exp_list_to_string p e_list)

let atom_to_string p a = match a with 
  | Aeq(e1,e2) -> (exp_to_string p e1) ^ " = " ^ (exp_to_string p e2)
  | Aneq(e1,e2) -> (exp_to_string p e1) ^ " == " ^  (exp_to_string p e2) (* check this! weird rankfinder syntax *)
  | Aless(e1,e2) -> (exp_to_string p e1) ^ " < " ^ (exp_to_string p e2)
  | Aleq(e1,e2) -> (exp_to_string p e1) ^ " =< " ^(exp_to_string p e2)

let rec atom_list_to_string p = function
  | [] -> ""
  | [se] -> atom_to_string p se
  | se::se_list -> (atom_to_string p se) ^ ", " ^ (atom_list_to_string p se_list)

let unop_filter = function
  | Cil.Neg -> true
  | Cil.BNot | Cil.LNot -> false

let binop_filter = function
  | Cil.PlusA | Cil.MinusA | Cil.Mult | Cil.Div -> true 
  | _ -> false

let rec exp_filter = function 
  | Var _ | Const_int _ -> true
  | Cast(typ,e1) -> exp_filter e1
  | UnOp(op,e1) -> (unop_filter op && exp_filter e1)
  | BinOp(op,e1,e2) -> (binop_filter op && exp_filter e1 && exp_filter e2)
  | Lvar _ | Fvar _ | Lfield _ | Lindex _ -> false

let atom_filter = function
  | Aeq(e1,e2) -> (exp_filter e1 && exp_filter e2)
  | Aneq _ -> false
  | Aless(e1,e2) | Aleq(e1,e2) -> (exp_filter e1 && exp_filter e2)
 
(* generate input from state p, write into file input_fname *)
let rankfinder_generate_input p input_fname output_fname space =
  let atoms_pure = 
    let atoms_pi = prop_get_pi p in 
    let sub = prop_get_sub p in
    let list_sub = sub_to_list sub in
    let f_pure atoms_acc (id,e) = Aeq(Var id,e)::atoms_acc 
    in List.rev (List.fold_left f_pure atoms_pi list_sub) in 
  let (atoms_sigma, renaming) = 
    let sigma = prop_get_sigma p in 
    let f_spatial acc = function
      | Hpointsto(Lvar pvar, Eexp e, typ) ->
          let var' = create_fresh_primed_ident (pvar_get_name pvar)
	  in (Aeq(Var var', e), (pvar,var',e,typ))::acc
      | _ -> assert false in
    let decls = List.rev (List.fold_left f_spatial [] sigma) in
    let atoms_sigma = List.map fst decls in
    let renaming = List.map snd decls
    in (atoms_sigma, renaming) in
  let str_constraint = 
    let atoms = atoms_pure @ atoms_sigma in
    let atoms' = List.filter atom_filter atoms in
    let str_atoms = atom_list_to_string p atoms'  
    in "constraint([" ^ str_atoms ^ "]), space(" ^ space ^ "), dump('" ^ output_fname ^ "')" in
  let str_from = 
    let f_from (x,_,_,_) = 
      let x_name = pvar_get_name x in
      let x0 = Var (get_default_footprint_ident x_name) 
      in x0 in
    let init_vars = List.map f_from renaming in
    let str_init_vars = exp_list_to_string p init_vars 
    in "from(" ^ str_init_vars ^ ")" in
  let str_to = 
    let f_to (_,x',_,_) = Var x' in
    let cur_vars = List.map f_to renaming in
    let str_cur_vars = exp_list_to_string p cur_vars
    in "to(" ^ str_cur_vars ^ ")" in
  let str = 
    "relation(" ^ str_from ^ ", " ^ str_to ^ ", " ^ str_constraint ^ ")." in
  let _ = 
    let oc = open_out input_fname 
    in 
      E.log "@..... RANKFINDER OUTPUT ....@.%s@." str;
      Printf.fprintf oc "%s" str;
      close_out oc
  in   
    renaming
	  
let rankfinder_buffer = String.create 1000

(* Run the rankfinder *)
let rankfinder_run input_fname =
  let oc_in = Unix.open_process_in (!Config.rankfinder_file ^ " " ^ input_fname) in
  let size_in = input oc_in rankfinder_buffer 0 1000 in 
  let str_in = String.sub rankfinder_buffer 0 size_in in 
  let wfregexp = Str.regexp "Ranking" 
  in 
    try 
     ignore(Unix.close_process_in oc_in);
     ignore(Str.search_forward wfregexp str_in 0);
     true
   with 
   | Not_found -> false



let read_output output_fname = 
  let remove_spaces str = Str.global_replace (Str.regexp " ") "" str in
  let file = open_in output_fname in
  let d0 =
    try int_of_string (remove_spaces (input_line file))
    with Failure "int_of_string" -> (-1) in
  let d =
    try int_of_string (remove_spaces (input_line file))
    with Failure "int_of_string" -> (-1) in
  let rec read_rank_coeffs () =
    try
      let line = remove_spaces (input_line file) in
      let coeff =
        try (int_of_string line)
        with Failure "int_of_string" -> 0 
      in
        coeff :: (read_rank_coeffs ())
    with 
      | End_of_file -> [] in
  let r = read_rank_coeffs () 
  in begin
    close_in file;
    E.log "@..... Ranking function read d0=%d d=%d r=[%s] ....@."
      d0 d (String.concat ", " (List.map string_of_int r));
    (d0, d, r)
  end

let rankfinder_generate_output p renaming output_fname = 
  let p_new_sigma = 
    let sid = prop_get_sid p in
    let p_emp = prop_emp sid in
    let f_sigma p_cur (x,x',e,typ) = 
      let x_name = pvar_get_name x in
      let x0 = get_default_footprint_ident x_name in
      let se = match e with
(*
       | Var x0' when ident_equal x0' x0 -> e
       | Const_int _ -> e
*)
       | _ -> Var x' in
      let hpred = mk_ptsto_lvar (x, typ, Some se)
      in prop_hpred_star p_cur hpred 
    in List.fold_left f_sigma p_emp (List.rev renaming) in
  let p_new_pi = 
    let (d0,d,coeffs) = read_output output_fname in
    let vars_coeffs = 
      try List.rev (List.combine renaming coeffs)
      with Invalid_argument _ -> assert false in
    let f_old exp ((pvar,_,_,_), coeff) =
      if coeff = 0 then exp 
      else 
        let pvar_name = pvar_get_name pvar in
        let var0 = get_default_footprint_ident pvar_name in
        let coeff_var0 = BinOp(Cil.Mult, Const_int coeff, Var var0) 
        in BinOp(Cil.PlusA, coeff_var0, exp) in
    let f_new exp ((_,var',_,_), coeff) = 
      if coeff = 0 then exp
      else
        let coeff_var' = BinOp(Cil.Mult, Const_int coeff, Var var') 
        in BinOp(Cil.PlusA, coeff_var', exp) in
    let d' = if d > 1 then 1 else d in
    let old_exp = List.fold_left f_old (Const_int (0-d')) vars_coeffs in
    let new_exp = List.fold_left f_new (Const_int 0) vars_coeffs in
    let p' = conjoin_leq new_exp old_exp p_new_sigma in
    let d0' = if d0 > -1000000 then -1000000 else d0
    in conjoin_less (Const_int d0') old_exp p' in 
  let p_new = 
    let f_eq p_cur (x,x',e,_) = 
      let x_name = pvar_get_name x in
      let x0 = get_default_footprint_ident x_name 
      in match e with
       | Var x0' when ident_equal x0' x0 -> 
	  conjoin_eq e (Var x') p_cur
       | Const_int n ->
	  conjoin_eq e (Var x') p_cur
       | _ -> p_cur
    in List.fold_left f_eq p_new_pi (List.rev renaming) 
  in
  let p_new' = 
          let visited = prop_get_visited p in 
          prop_set_visited p_new visited
  in  E.log "@..... [rankfinder_generate_output] prop: %a ....@." pp_prop p_new'; 
     p_new'

(* produces rankfinder input from a prop *)
let rankfinder sid p =
  let input_fname = "rankfinder.in" in
  let output_fname = "rankfinder.out" in
  let renaming = 
    if (!Config.rankfinder = 0 || !Config.rankfinder >= 2) 
    then rankfinder_generate_input p input_fname output_fname "int" 
    else rankfinder_generate_input p input_fname output_fname "rat" in 
  let succeed  = rankfinder_run input_fname in 
  if succeed then 
    Some (Prop.prop_set_wf (rankfinder_generate_output p renaming output_fname) true)
  else if (!Config.rankfinder >= 2) then 
    begin
    let renaming2 = rankfinder_generate_input p input_fname output_fname "rat" in
    let succeed2  = rankfinder_run input_fname in 
    if succeed2 then 
      begin 
      let new_p = rankfinder_generate_output p renaming output_fname in
      E.err "@[<2>#### RANKFINDER RETRY (statement %d) ####@\n" sid;
      E.err "OLD PROP: %a@\n@\n" pp_prop p;
      E.err "NEW PROP: %a@\n@." pp_prop new_p;
      Some(Prop.prop_set_wf new_p true)
      end 
    else 
      begin
      E.err "@.#### ERROR: TERMINATION BUG at statement %d ####@." sid;
      E.err "@.%a@.@." pp_prop p;
      (*assert false*)
		  Some(Prop.prop_set_wf p false)
      end
    end
  else 
    begin
    E.err "@.#### ERROR: TERMINATION BUG at statement %d ####@." sid;
    E.err "@.%a@.@." pp_prop p;
    (*assert false*)
	  Some(Prop.prop_set_wf p false)
    end

let just_rankfinder p = 
	let input_fname1 = "rankfinder_int.in" in 
	let input_fname2 = "rankfinder_rat.in" in 
	let r1 = rankfinder_generate_input p input_fname1 "test1" "int" in 
	let r2 = rankfinder_generate_input p input_fname1 "test2" "rat" in 
	(rankfinder_run input_fname1) & (rankfinder_run input_fname2)
	

