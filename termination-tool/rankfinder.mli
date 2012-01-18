open Prop
open Sil

val exp_to_string : prop -> exp -> string
val rankfinder : int -> prop -> prop option
val just_rankfinder : prop -> bool 
