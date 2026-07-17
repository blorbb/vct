open Datatypes
open PeanoNat

module Coq__1 : sig
 type t =
 | Pos of int
 | Neg of int
end
include module type of struct include Coq__1 end

val negate : t -> t

val atm : t -> int

val eqb : t -> t -> bool

val eq_dec : t -> t -> bool

val compare : t -> t -> comparison

module Ordered :
 sig
  type t = Coq__1.t

  val eq_dec : Coq__1.t -> Coq__1.t -> bool

  val compare : Coq__1.t -> Coq__1.t -> comparison
 end
