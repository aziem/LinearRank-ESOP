(* Intraprocedural analysis for termination *)

open Pretty
open Cil

module U = Util
module IH = Inthash

module E = Error

type t = Propset.propset








(* =============== BEGIN: Module Loop =============== *)

(* This module keeps all the backedges for each loop. *)

module Loop = struct

  let bedges : (int list) IH.t = IH.create 100

  let bedges_clear _ = IH.clear bedges

  let bedges_replace (sid : int) (ids : int list) : unit = 
    IH.replace bedges sid ids

  let bedges_retrieve (sid : int) : int list = 
    try 
      IH.find bedges sid
    with Not_found ->
      (bedges_replace sid []);
      []

  let rec bedges_compute_stmt (sid : int) (s : stmt) : int list =
    let bstmts = 
      let predicate stmt = (sid = stmt.sid)
      in if List.exists predicate s.succs then [s.sid] else [] 
    in match s.skind with
      | Instr _ | Return _ | Goto _ | Break _ | Continue _ -> 
	  bstmts
      | If (_, tblk, fblk, _) ->
          let bstmts_t = bedges_compute_block sid tblk in
	  let bstmts_f = bedges_compute_block sid fblk 
	  in bstmts@bstmts_t@bstmts_f
      | Switch (_,blk,_,_) | Loop (blk,_,_,_) | Block (blk) ->
	  let bstmts_blk = bedges_compute_block sid blk
	  in bstmts@bstmts_blk
      | TryFinally (blk1,blk2,_) | TryExcept (blk1,_,blk2,_) ->
          let bstmts1 = bedges_compute_block sid blk1 in
	  let bstmts2 = bedges_compute_block sid blk2 
	  in bstmts@bstmts1@bstmts2

  and bedges_compute_block (sid : int) (b : block) : int list =
    bedges_compute_stmts sid b.bstmts

  and bedges_compute_stmts (sid : int) (stmts : stmt list) : int list =
    List.flatten (List.map (bedges_compute_stmt sid) stmts)

  let bedges_compute_insert (sid : int) (b : block) : unit =
    let sids = bedges_compute_block sid b in
    let sids' = List.sort Ident.int_compare sids 
    in bedges_replace sid sids'

  class loopVisitor = object
    inherit nopCilVisitor

    method vstmt (s : stmt) : stmt visitAction =
      match s.skind with 
	| Loop (blk, _, Some cont_stmt, _) -> 
	    bedges_compute_insert cont_stmt.sid blk;  
	    DoChildren
	| Loop _ -> assert false
	| _ -> DoChildren	    
  end

  let reset _ : unit = 
    bedges_clear ()

  let compute (f : fundec) : unit =
    let visitor = new loopVisitor 
    in ignore(visitCilFunction visitor f)

  let get (sid : int) : int list =
    bedges_retrieve sid
      
end

(* =============== END: Module Loop =============== *)





(* =============== BEGIN: Object workset =============== *)

module WorkSet =
  Set.Make(struct
    type t = Cil.stmt
    let compare = (fun s1 s2 -> Ident.int_compare s1.sid s2.sid)
  end)

let workset : WorkSet.t ref = ref WorkSet.empty

let workset_add s =
  workset := WorkSet.add s !workset

let workset_reset () = 
  workset := WorkSet.empty

let workset_take () = 
  let min = WorkSet.min_elt !workset 
  in
    workset := WorkSet.remove min !workset;
    min

let workset_empty () =
  WorkSet.is_empty !workset

(* =============== END: Object workset =============== *)


let add_visited_sid (i:int) (p:Prop.prop) = 
        Prop.prop_addvisited p i



(* =============== BEGIN: Module StmtData =============== *)

(* This module maintains all the data used by the analyzer *)

module StmtData = struct
	let func : fundec option ref = ref None
		
	let numbadprops : int ref = ref 0

  let total_states : int ref = ref 0

  let tbl_done : t IH.t = IH.create 100

  let tbl_todo : t IH.t = IH.create 100

  let tbl_loop : t IH.t = IH.create 100

  let tbl_obs : t IH.t = IH.create 100
	
	let fundec_set f = 
			func := Some(f)
	
  let htable_replace (htable : t IH.t) (s : stmt) (d : t) : unit = 
    IH.replace htable s.sid d

  let htable_retrieve (htable : t IH.t) (s : stmt) : t = 
    try 
      IH.find htable s.sid
    with Not_found ->
      htable_replace htable s Propset.propset_empty;
      Propset.propset_empty

  let rec notify_obs (loop : stmt) (obs : t) (loop_sum : t) : unit =
    let d = SymExec.lifted_compose obs loop_sum in
    let succ_stmt = match loop.succs with
      | [] -> assert false
      | [s] -> s
      | _ -> assert false
    in put_todo loop succ_stmt d

  and register_obs (loop : stmt) (new_obs : t) : unit = 
    let obs = htable_retrieve tbl_obs loop in
    let loop_sum = htable_retrieve tbl_loop loop in
    let new_obs' = Propset.propset_diff new_obs obs in
    let obs' = Propset.propset_union new_obs' obs 
    (*let obs' = Propset.propset_map (add_visited_sid loop.sid) obs''*)
    in 
      notify_obs loop new_obs' loop_sum;
      htable_replace tbl_obs loop obs'

  and register_loop (loop : stmt) (new_loop_sum : t) : unit =
    let obs = htable_retrieve tbl_obs loop in
    let loop_sum = htable_retrieve tbl_loop loop in
    let new_loop_sum' = Propset.propset_diff new_loop_sum loop_sum in
    let loop_sum' = Propset.propset_union new_loop_sum' loop_sum 
    (*let loop_sum' = Propset.propset_map (add_visited_sid loop.sid)
     * loop_sum''*)
    in 
      notify_obs loop obs new_loop_sum';
      htable_replace tbl_loop loop loop_sum'

  and put_todo (from_s : stmt) (s : stmt) (d : t) : unit =
    let d' = SymExec.lifted_rename_primed_vars d in
    let d = Propset.propset_map (add_visited_sid s.sid) d' in 
    let update_print_stat visited todo gen_d new_d =
      total_states := !total_states + (Propset.propset_size new_d);
      E.log " tot:%d old:%d gen:%d new:%d ####@." 
   	!total_states 
 	((Propset.propset_size visited) + (Propset.propset_size todo))
 	(Propset.propset_size gen_d)
 	(Propset.propset_size new_d);
      E.log "@..... Old Visited Abstract Value ....@.@.%a@." Propset.pp_propset visited;
      E.log "@..... Old Todo Abstract Value ....@.@.%a@." Propset.pp_propset todo;
      E.log "@..... New Abstract Value ....@.@.%a@." Propset.pp_propset new_d
    in
    let do_noloop _ =
      let visited = htable_retrieve tbl_done s in
      let todo = htable_retrieve tbl_todo s in
      let d' = Propset.propset_diff (Propset.propset_diff d visited) todo in 
      (*let d'' = Propset.propset_map (add_visited_sid s.sid) d'' in*)
      let todo' = Propset.propset_union d' todo 
      in 
	E.log "@.#### [STATEMEMT from %d to %d] (noloop)" from_s.sid s.sid; 
        update_print_stat visited todo d d';
	htable_replace tbl_todo s todo';
	Propset.propset_is_empty todo'
    in
    let do_loop_back _ =
      (*print_string "NEXT ITERATION\n";*)
      let filter p = (Prop.prop_get_sid p = s.sid) in
      let d_sum = Propset.propset_filter filter d in
      let d_abs = Abs.lifted_abstract s.sid d_sum in
		  let cont = Propset.propset_filter (fun p -> not(Prop.prop_is_wf p)) d_abs in 
		  (* have a termination bug *)
			if (Propset.propset_size cont) !=0 then 
				begin
					let f = match !func with 
						| None -> assert false
						| Some(fd) -> fd 
					in 
					let outputerror_graph (p:Prop.prop) = 
							let v = Prop.prop_get_visited p in 
							Dotty.printCfgFilename (f.svar.vname ^ (string_of_int !numbadprops) ^ ".dot") f v ;
							numbadprops := !numbadprops + 1
					in 
					Propset.propset_iter outputerror_graph cont;
					assert false
				end
			else
			begin
      	let visited = htable_retrieve tbl_done s in
      	let todo = htable_retrieve tbl_todo s in
      	let d_sum' = Propset.propset_diff (Propset.propset_diff d_abs visited) todo in 
      	(*let d_sum'' = Propset.propset_map (add_visited_sid s.sid) d_sum'' in*)
      	let todo' = Propset.propset_union d_sum' todo  
      	in 
					E.log "@.#### [STATEMEMT from %d to %d] (loop_cont,back)" from_s.sid s.sid; 
        	ignore(Pretty.printf "St from: %a\n" d_stmt from_s);
        	ignore(Pretty.printf "St to: %a\n" d_stmt s);
        	update_print_stat visited todo d_sum d_sum';
					htable_replace tbl_todo s todo';
					register_loop s d_sum';
					Propset.propset_is_empty todo'
			end
    in
    let do_loop_noback _ = 
      let filter p = (Prop.prop_get_sid p = s.sid) in
      let d_sum = Propset.propset_filter filter d in
      let d_obs = Propset.propset_diff d d_sum in
      let visited = htable_retrieve tbl_done s in
      let todo = htable_retrieve tbl_todo s in
      let d' = Propset.propset_diff (Propset.propset_diff d visited) todo in
      (*let d'' = Propset.propset_map (add_visited_sid s.sid) d'' in*)
      let d_sum' = Propset.propset_diff (Propset.propset_diff d_sum visited) todo in 
      let d_obs' = Propset.propset_diff (Propset.propset_diff d_obs visited) todo in
      let visited' = Propset.propset_union d_obs' visited in  
      let todo' = Propset.propset_union d_sum' todo  
      in 
	E.log "@.#### [STATEMEMT from %d to %d] (loop_cont,noback)" from_s.sid s.sid; 
        update_print_stat visited todo d d';
	htable_replace tbl_done s visited';
	htable_replace tbl_todo s todo';
	register_obs s d_obs';
	Propset.propset_is_empty todo'
    in
    let update_workset flag =
      if flag then () else workset_add s
    in 
    let bedges = Loop.get s.sid 
    in 
      match bedges with
	| [] -> update_workset (do_noloop ())
	| _ -> 
	    if List.mem from_s.sid bedges
	    then update_workset (do_loop_back ())
	    else update_workset (do_loop_noback ())

  let checkout_todo (sid:int) : t = 
    try
      let visited = IH.find tbl_done sid in
      let todo = IH.find tbl_todo sid in
      let new_visited = Propset.propset_union visited todo in
      let _ = 
	IH.replace tbl_done sid new_visited;
        IH.replace tbl_todo sid Propset.propset_empty 
      in todo
    with Not_found -> 
      assert false
	
  let is_empty_todo (sid:int) : bool = 
    try 
      let todo = IH.find tbl_todo sid 
      in Propset.propset_is_empty todo
    with Not_found ->
      false

  let reset _ =
    IH.clear tbl_todo;
    IH.clear tbl_done;
    IH.clear tbl_loop;
    IH.clear tbl_obs

  let get_result (s : stmt) : t = 
    htable_retrieve tbl_done s 

end

(* =============== END: Module StmtData =============== *)




(* =============== BEGIN: Main Part of the Analysis =============== *)


(* Next method does not seem to use sid for anything! *)
let doInstr (sid:int) (i: instr) (d: t) = 
  (*ignore(Pretty.printf "Instruction: %a\n" d_instr i);
  ignore(Pretty.printf "Sid: %d\n" sid);*)
  let (ids,instrs) = Trans.trans_instr dummyFunDec i in
  let _ = 
    E.log "@.#### Symbolic Execution ####@.";
    E.log "@..... Pre Abstract Value .... @.%a@." Propset.pp_propset d;
    E.log "@..... Translated Instrs ....@.%a@." Sil.pp_instr_list instrs in
  let post_d = List.fold_left SymExec.lifted_sym_exec d instrs in
  let new_d = SymExec.lifted_exist_quantify (Sil.fav_from_list ids) post_d in
  let new_d' = Propset.propset_map (add_visited_sid sid) new_d in 
  let _ = 
    E.log "@..... Post Abstract Value ....@.%a@." Propset.pp_propset new_d;
  in new_d    

let doGuard (sid:int) (e: exp) (pre_d: t) = 
  (*ignore(Pretty.printf "Boolean Expression: %a\n" d_exp e);*)
  let ((ids,instrs), condition) = Trans.trans_exp dummyFunDec e in
  let _ = 
    E.log "@.#### Pruning ####@.@.";
    E.log "@..... Generated Instrs .... @.%a@." Sil.pp_instr_list instrs;
    E.log "@..... Generated Condition .... @.%a@." Sil.pp_exp condition;
    E.log "@..... Before Prunning .... @.%a@." Propset.pp_propset pre_d in
  let post_d = List.fold_left SymExec.lifted_sym_exec pre_d instrs in
  let pruned_d = SymExec.prune condition post_d in
  let quantified_d = SymExec.lifted_exist_quantify (Sil.fav_from_list ids) pruned_d in  
  let quantified_d' = Propset.propset_map (add_visited_sid sid) quantified_d 
  in
    E.log "@..... After Prunning .... @.%a@." Propset.pp_propset quantified_d;
    quantified_d


(* We call this function when we have encountered a statement, with
 * some state. *)
let reachedStatement (from_s: stmt) (s: stmt) (d: t) : unit = 
  StmtData.put_todo from_s s d 

(* Get the two successors of an If statement *)
let ifSuccs (s:stmt) : stmt * stmt = 
  let fstStmt blk = match blk.bstmts with
    | [] -> Cil.dummyStmt
    | fst::_ -> fst
  in match s.skind with
    | If(e, b1, b2, _) ->
        let thenSucc = fstStmt b1 in
        let elseSucc = fstStmt b2 in
        let oneFallthrough () = 
          let fallthrough = 
	    List.filter 
              (fun s' -> thenSucc != s' && elseSucc != s')
              s.succs
          in match fallthrough with
	    | [] -> (E.err "@.#### ERROR (Bad CFG): missing fallthrough for If. ####@.@."; assert false)
	    | [s'] -> s'
	    | _ -> (E.err "@.#### ERROR (Bad CFG): multiple fallthrough for If. ####@.@."; assert false) in
        let stmtOrFallthrough s' =
          (* If thenSucc or elseSucc is Cil.dummyStmt, it's an
	   * empty block.  So the successor is the statement after
	   * the if *)
          if s' == Cil.dummyStmt then
	    oneFallthrough ()
          else 
	    s'
        in
          (stmtOrFallthrough thenSucc,
          stmtOrFallthrough elseSucc)	
    | _ -> (E.err "@.#### ERROR: ifSuccs on a non-If Statement. ####@.@."; assert false)

(* Process a statement *)
let processStmt (s: stmt) : unit = 
  let sid = s.sid in 
  let curr = StmtData.checkout_todo sid in
  let handleInstruction (d: t) (i: instr) : t =  
    (* Do the instructions in order *)
      doInstr sid i d in
    let after: t = match s.skind with 
      | Instr il -> 
          (* Handle instructions starting with the first one *)
          List.fold_left handleInstruction curr il
      | Goto _ | Break _ | Continue _ | If _ 
      | TryExcept _ | TryFinally _ 
      | Switch _ | Loop _ | Return _ | Block _ -> curr in
    let succsToReach = match s.skind with (* Handle If guards *)
      |  If (e, _, _, _) ->
           let not_e = UnOp(LNot, e, intType) in
           let d_then = doGuard sid e after in
           let d_else = doGuard sid not_e after in
	   let thenSucc, elseSucc = ifSuccs s  
	   in begin
	     reachedStatement s thenSucc d_then;
	     reachedStatement s elseSucc d_else;
	     []
	   end		   
      | _ -> s.succs
    in
      (* Reach the successors *)
      List.iter (fun s' -> reachedStatement s s' after) succsToReach
	

let doAnalysis _ =
  let rec fixedpoint () =
    let sopt = 
      try Some (workset_take ())
      with not_found -> None
    in match sopt with
      | Some s ->
          (*print_string "WORKSET : ";
          print_string (string_of_int s.sid);
          print_string "\n";
          ignore(Pretty.printf "Statement from workset : %a\n" d_stmt s);*)
          processStmt s;
          fixedpoint ()
      | None -> ()
  in
    fixedpoint ()     

(* =============== END: Main Part of the Analysis =============== *)





(* =============== BEGIN: compute_variant (Top-level Function for Anaysis) =============== *)


let loop_stmts = ref []

class loopFinderClass = object(self)
  inherit nopCilVisitor

  method vstmt s = match s.skind with
    | Loop _ -> 
	(loop_stmts := s::(!loop_stmts);
         DoChildren)
    | _ -> DoChildren
end

(* computes the list of the loop statements from a function *)
let find_loops (f : fundec) : stmt list =
  loop_stmts := [];
  ignore(visitCilFunction (new loopFinderClass) f);
  !loop_stmts


let loop_cont_stmts = ref []

class loopContFinderClass = object(self)
  inherit nopCilVisitor

  method vstmt s = match s.skind with
    | Loop (_,_,Some cont,_) -> 
	(loop_cont_stmts := cont::(!loop_cont_stmts);
         DoChildren)
    | Loop _ -> assert false
    | _ -> DoChildren
end

(* computes the list of the continue "labels" of loop statements from a function *)
let find_loop_conts (f : fundec) : stmt list =
  loop_cont_stmts := [];
  ignore(visitCilFunction (new loopContFinderClass) f);
  !loop_cont_stmts


let compute_variants (f: fundec) : unit =

  let initialize _ =
    let f_CFG _ =
      prepareCFG f;
      computeCFGInfo f false in
    let f_Loop _ =
      Loop.reset ();
      Loop.compute f in
    let f_workset _ =
      workset_reset () in
    let f_StmtData _ =   
      let generate_init_pset sid =  
	let pset_emp = Propset.propset_singleton (Prop.prop_emp sid) in 
	let mk_decl x =
	  let xname = Ident.string_to_name x.vname in
    let pvar = Sil.mk_pvar xname dummyFunDec in
	  let gvar = Sil.Var (Ident.get_default_footprint_ident xname) in
    let pvar_t = Trans.trans_typ [] x.vtype 
    in (pvar, pvar_t, Some gvar) 
	in 
	let formals = List.map mk_decl f.sformals in 
	let locals = List.map mk_decl f.slocals in
	let alloc_formals_locals = Prop.prop_init_formals_locals formals locals 
	in (Propset.propset_map alloc_formals_locals pset_emp) in
      let handle_loop loop_cont = 
	let init_pset = generate_init_pset loop_cont.sid 
	in StmtData.put_todo loop_cont loop_cont init_pset in
      let loop_conts = find_loop_conts f 
      in 
	StmtData.reset ();
	List.iter handle_loop loop_conts
    in    
      f_CFG ();
			StmtData.fundec_set f;
      Dotty.printCfgFilename (f.svar.vname ^ ".dot") f [];
      f_Loop ();
      f_workset ();
      f_StmtData ()
  in 

  let execute _ = 
      try
				doAnalysis ();
				E.err "@.#### [FUNCTION %s] ...OK #####@." f.svar.vname
      with 
				| _ -> (E.err "@.#### [FUNCTION %s] ...ERROR ####@." f.svar.vname; assert false)
  in

  let collect_print_results _ = 
    let loop_conts = find_loop_conts f in
    let print_result n stmt size pset =
      let nth = match n with
				| 1 -> "st"
				| 2 -> "nd"
				| 3 -> "rd"
				| _ -> "th"
      in
		E.err "@.... [FUNCTION] Analysis result at the %d%s loop cont stmt....@." n nth;
		E.err "@.%a@." Propset.pp_propset pset;
		E.err "@.... [STATISTICS] Num of States: %d....@." size;
	() in
    let print_result n stmt = 
      try 
				let pset = StmtData.get_result stmt in
				let size = Propset.propset_size pset 
				in 
	  		print_result n stmt size pset; 
	  		n+1
      with Not_found -> n 
    in 
      ignore(List.fold_left print_result 1 loop_conts) 
  in 

    match (find_loops f) with
      | [] -> (* Function f has no loops *)
	  E.err "@.#### [FUNCTION %s] ...Analysis Start ####@." f.svar.vname;
	  E.err "@.#### [FUNCTION %s] ...Analysis Finished (No Loops) ####@." f.svar.vname
      | start :: _ -> (* Function f has loops *)
          try
            E.err "@.#### [FUNCTION %s] ...Analysis Start ####@." f.svar.vname;
            initialize ();
            execute ();
            E.err "@.#### [FUNCTION %s] ... Analysis Finished ####@." f.svar.vname;
            collect_print_results ();
	    E.err "@.#### Termination Proved ####@.";
            print_string "\nTERMINATION PROVED\n"
          with _ ->
	    E.err "@.#### Failed to Prove Termination ####@.";
            print_string "\nFAILED TO PROVE TERMINATION\n\n"


(* =============== END: compute_variant (Top-level Function for Anaysis) =============== *)





(* =============== BEGIN: the main CIL top-level routines =============== *)

class analysisVisitor = object
  inherit nopCilVisitor
    
  method vfunc (f: fundec) : fundec visitAction =
    compute_variants(f);
    SkipChildren

  method vglob (g: global) : global list visitAction = begin
    match g with
      | GType(ti,_) ->        
	  let _ = Trans.trans_typeinfo [] ti        
	  in SkipChildren
      | GCompTag _ 
      | GCompTagDecl _
      | GEnumTag _
      | GEnumTagDecl _
      | GVarDecl _
      | GVar _ 
      | GFun _ 
      | GAsm _ 
      | GPragma _ 
      | GText _ -> DoChildren
  end
end



let feature : featureDescr = 
  { fd_name = "terminationanalysis";
    fd_enabled = ref false;
    fd_description = "termination analysis";
    fd_extraopt = [
	"--dumpfile",Arg.String (fun n -> Config.dump_file :=n),
	"the file that the source is dumped to *after* Cfg transformation";
	"--test", Arg.Int (fun n -> Config.test := n), 
        "the control of the print (default = 2: don't print log nor err)";
	"--rankfinder", Arg.Int (fun n -> Config.rankfinder := n), 
        "the control for calling the rankfinder (default = 2:  use Int first and Rat next)";
	"--prover", Arg.Int (fun n -> Config.prover := n), 
        "the power of the prover. (default = 2: use Z3.  )";];
    fd_doit = 
      (function (f: file) -> 
	print_string (f.fileName);
	let aVisitor = new analysisVisitor 
        in visitCilFileSameGlobals aVisitor f;
        let channel = open_out (!Config.dump_file) in 
        Cil.dumpFile defaultCilPrinter channel "hello.txt" f;
       );
    fd_post_check = false
  } 

(* =============== END: the main CIL top-level routines =============== *)
