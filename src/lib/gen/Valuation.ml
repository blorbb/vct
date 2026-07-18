open Atom
open List

type t = int list

(** val forces_atm : t -> int -> bool **)

let forces_atm v p =
  existsb (eqb p) v
