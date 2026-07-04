open ListDef
open ListExt
open Lit
open Utils

type t = Lit.t list

(** val max_atm : t -> int **)

let max_atm phi =
  apply (map atm phi) list_max_nat
