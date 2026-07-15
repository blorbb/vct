open Datatypes

module type UsualOrderedTypeFull =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end
