(** Module for Names and Identifiers *)

type name = int

type kind = PRIMED | NORMAL | FOOTPRINT

type ident =
    {kind: kind;
     name: name;
     stamp: int}

(** {2 Comparison Functions} *)

let string_equal (s1:string) (s2:string) = s1=s2

let (=) (i:int) (j:int) = Pervasives.(=) i j

(** Compare police: generic compare disabled. *)
let compare = ()

(** Efficient comparison for integers *)
let int_compare (i:int) (j:int) =
  if i<j then -1
  else if i=j then 0
  else 1

let name_compare = int_compare

let name_equal (n1:name) (n2:name) = n1=n2

let kind_compare k1 k2 = match k1,k2 with
  | PRIMED,PRIMED -> 0
  | PRIMED,_ -> -1
  | _,PRIMED -> 1
  | NORMAL,NORMAL -> 0
  | NORMAL,_ -> -1
  | _,NORMAL -> 1
  | FOOTPRINT,FOOTPRINT -> 0

let kind_equal k1 k2 = (kind_compare k1 k2 = 0)

let ident_compare i1 i2 =
  let n = kind_compare i2.kind i1.kind
  in if n<>0 then n
    else 
      let n = name_compare i1.name i2.name
      in if n<>0 then n
	else int_compare i1.stamp i2.stamp

let ident_equal i1 i2 =
  ident_compare i1 i2 = 0

let rec ident_list_compare il1 il2 = match il1,il2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | i1::l1, i2::l2 ->
      let n = ident_compare i1 i2
      in if n<>0 then n
	else ident_list_compare l1 l2

let ident_list_equal ids1 ids2 = (ident_list_compare ids1 ids2 = 0)


(** {2 Conversion between Names and Strings} *)

module StringHash =
  Hashtbl.Make(struct
    type t = string
    let equal (s1:string) (s2:string) = string_equal s1 s2
    let hash = Hashtbl.hash
  end)

module NameHash =
  Hashtbl.Make(struct
    type t = name
    let equal = name_equal
    let hash = Hashtbl.hash
  end)

type string_name_map =
    { next_available_name: int ref;
      string_to_name: name StringHash.t;
      name_to_string: string NameHash.t }

(** Bijection between names and strings. *)
let string_name_map =
  { next_available_name = ref max_int;
    string_to_name = StringHash.create 1000;
    name_to_string = NameHash.create 1000}

(** Convert a string to a name using counter [next_available]. *)
let string_to_name (s:string) = 
  try StringHash.find string_name_map.string_to_name s
  with Not_found ->
    let name = !(string_name_map.next_available_name) 
    in
      decr string_name_map.next_available_name;
      StringHash.add string_name_map.string_to_name s name;
      NameHash.add string_name_map.name_to_string name s;
      name

(** Convert a name to a string. *)
let name_to_string (name:name) = 
  try NameHash.find string_name_map.name_to_string name
  with Not_found -> 
    assert false (* All available names should be defined before. *)


(** {2 Functions and Hash Tables for Managing Stamps} *)

(** Set the stamp of the identifier *)
let ident_set_stamp i stamp =
  {i with stamp=stamp}

(** Get the stamp of the identifier *)
let ident_get_stamp i =
  i.stamp

(** Map from names to stamps. *)
let name_map = NameHash.create 1000

(** {2 Functions for Identifiers} *)

(** Get a name of an identifier *)
let ident_name id =
  id.name

let ident_kind id =
  id.kind

let ident_is_primed (id:ident) =
  kind_equal id.kind PRIMED

let make_ident_primed id =
  if kind_equal id.kind PRIMED then assert false
  else {id with kind=PRIMED}

let make_ident_unprimed id =
  if not (kind_equal id.kind PRIMED) then assert false
  else {id with kind=NORMAL}

(** Return a footprint identifier that is deterimined the given name.
    This identifier is used to keep the initial value of program
    variable [name]. *)
let get_default_footprint_ident name =
  {kind=FOOTPRINT; name=name; stamp=0}

(** Create a fresh identifier with the given kind and name. *)
let create_fresh_ident kind name =
  let stamp =
    try
      let stamp = NameHash.find name_map name
      in NameHash.replace name_map name (stamp+1);
	stamp+1
    with Not_found ->
      NameHash.add name_map name 1;
      1
  in {kind=kind; name=name; stamp=stamp}

(** Create a fresh normal identifier with the given name. *)
let create_fresh_normal_ident name =
  create_fresh_ident NORMAL name

(** Create a fresh primed identifier with the given name. *)
let create_fresh_primed_ident name =
  create_fresh_ident PRIMED name

(** {2 Pretty Printing} *)
open Format

(** Convert an identifier to a string. *)
let ident_to_string id =
  let base_name = name_to_string id.name in
  let prefix = match id.kind with
    | FOOTPRINT -> "@"
    | NORMAL -> ""
    | PRIMED -> "_" in
  let suffix = "_" ^ (string_of_int id.stamp)
  in prefix ^ base_name ^ suffix

(** Convert an identifer to a rankfinder-happy string. *)
let ident_to_rankfinder_string id = 
  let base_name = String.uppercase (name_to_string id.name) in
  let prefix = match id.kind with
    | FOOTPRINT -> "F"
    | NORMAL -> "N"
    | PRIMED -> "P" in
  let suffix = string_of_int id.stamp
  in prefix ^ base_name ^ suffix

(** Print a sequence. *)
let rec pp_seq pp f = function
  | [] -> ()
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a,%a" pp x (pp_seq pp) l

(** Pretty print a name. *)
let pp_name f name = fprintf f "%s" (name_to_string name)

(** Pretty print an identifier. *)
let pp_ident f id = fprintf f "%s" (ident_to_string id)

(** pretty printer for lists of identifiers *)
let pp_ident_list = pp_seq pp_ident

(** pretty printer for lists of names *)
let pp_name_list = pp_seq pp_name

