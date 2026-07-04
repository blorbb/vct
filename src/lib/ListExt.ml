open List
open PeanoNat

(** val list_max_nat : int list -> int **)

let list_max_nat l =
  fold_left Nat.max l 0
