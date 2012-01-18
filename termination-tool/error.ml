(** Can be applied to any number of arguments and throws them all away *)
let rec throw_away x = Obj.magic throw_away

let log fmt =
  if (!Config.test <= 0) 
  then Format.fprintf Format.std_formatter fmt
  else Obj.magic throw_away

let err fmt =
  if (!Config.test <= 1)
  then Format.fprintf Format.std_formatter fmt
  else Obj.magic throw_away

