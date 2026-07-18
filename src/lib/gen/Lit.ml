open Atom
open Datatypes

module Coq__1 = struct
 type t =
 | Pos of int
 | Neg of int
end
include Coq__1

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

(** val eq_dec : t -> t -> bool **)

let eq_dec a b =
  match a with
  | Pos p -> (match b with
              | Pos p0 -> eq_dec p p0
              | Neg _ -> false)
  | Neg p -> (match b with
              | Pos _ -> false
              | Neg p0 -> eq_dec p p0)

(** val compare : t -> t -> comparison **)

let compare x y =
  match x with
  | Pos p -> (match y with
              | Pos q -> compare p q
              | Neg _ -> Lt)
  | Neg p -> (match y with
              | Pos _ -> Gt
              | Neg q -> compare p q)

module Ordered =
 struct
  type t = Coq__1.t

  (** val eq_dec : Coq__1.t -> Coq__1.t -> bool **)

  let eq_dec =
    eq_dec

  (** val compare : Coq__1.t -> Coq__1.t -> comparison **)

  let compare =
    compare
 end
