module C = Cil
module F = Frontc


let parseOneFile (fname:string) : C.file = 
  let cil = F.parse fname () in 
  cil


let analyse (f: C.file) = 
  print_string (f.C.fileName);
  let aVisitor = new Analysis.analysisVisitor in 
  Cil.visitCilFileSameGlobals aVisitor f;
  let channel = open_out (!Config.dump_file) in 
  Cil.dumpFile Cil.defaultCilPrinter channel "hello.txt" f


let program_file_name = ref ""

let set_file_name n = program_file_name := n


let arg_list = [("-f", Arg.String(set_file_name), "program file name");]


let _ = 
  let usage_msg = "Usage: -f <file_name>" in 
  let _ = Arg.parse arg_list (fun s -> ()) usage_msg in 
   if (!program_file_name="") then
	Printf.printf "\n Program or Precondition file name not given...\n %s \n" usage_msg 
   else
     let f = parseOneFile !program_file_name in 
     analyse f
