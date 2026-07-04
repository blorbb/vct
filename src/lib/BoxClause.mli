open Datatypes
open Lit
open PeanoNat

type t = int * Lit.t

val max_atm : t -> int
