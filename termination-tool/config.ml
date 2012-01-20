(** Flag for the test mode 
    0 - Print all the outputs. Allow printing from log and err.
    1 - Do not print log. Allow printing only from err.
    2 - Do not print log nor err. 
*)
let test = ref 2

(** Flag for the prover mode.
    0 - use the default prover from sil.
    1 - use the default prover and simplify.
    2 - use Z3
*)
let prover = ref 2

(** Flag for calling the rankfinder.
    0 - call the rankfinder with Int.
    1 - call the rankfinder with Rat.
    2 - call the rankfinder first with Int, and then with Rat.
*)
let rankfinder = ref 2

let rankfinder_file = ref "/home/aziem/work/projects/LinearRank-ESOP/termination-tool/rankfinder"

let simplify_file = ref "/home/aziem/work/projects/LinearRank-ESOP/termination-tool/Simplify"

let z3_file = ref "/home/aziem/work/projects/LinearRank-ESOP/termination-tool/z3/bin/z3"

let dump_file = ref "file.cil"
