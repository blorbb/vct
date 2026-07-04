open Datatypes
open Lit
open PeanoNat

type t = int * Lit.t

(** val max_atm : t -> int **)

let max_atm phi =
  Nat.max (fst phi) (atm (snd phi))
