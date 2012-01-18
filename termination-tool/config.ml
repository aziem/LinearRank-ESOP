(** Flag for the test mode 
    0 - Print all the outputs. Allow printing from log and err.
    1 - Do not print log. Allow printing only from err.
    2 - Do not print log nor err. 
*)
let test = ref 2

(** Flag for the prover mode.
    0 - use the default prover from sil.
    1 - use the default prover and simplify.
*)
let prover = ref 1

(** Flag for calling the rankfinder.
    0 - call the rankfinder with Int.
    1 - call the rankfinder with Rat.
    2 - call the rankfinder first with Int, and then with Rat.
*)
let rankfinder = ref 2

let rankfinder_file = ref "/home/aziem/work/qm/esop-tool/termination-tool/rankfinder"

let simplify_file = ref "/home/aziem/work/qm/esop-tool/termination-tool/Simplify"

let dump_file = ref "file.cil"
