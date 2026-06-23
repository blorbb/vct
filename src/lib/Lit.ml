open Nat

type t =
| Pos of int
| Neg of int

(** val negate : t -> t **)

let negate = function
| Pos n -> Neg n
| Neg n -> Pos n

(** val atm : t -> int **)

let atm = function
| Pos n -> n
| Neg n -> n

(** val eqb : t -> t -> bool **)

let eqb a b =
  match a with
  | Pos p -> (match b with
              | Pos q -> eqb p q
              | Neg _ -> false)
  | Neg p -> (match b with
              | Pos _ -> false
              | Neg q -> eqb p q)
