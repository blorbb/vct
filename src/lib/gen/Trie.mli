open Datatypes
open Orders

module Make :
 functor (K:UsualOrderedTypeFull) ->
 sig
  module K' :
   sig
    type t = K.t

    val compare : K.t -> K.t -> comparison

    val eq_dec : K.t -> K.t -> bool
   end

  module KFacts :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = K.t

        val compare : K.t -> K.t -> comparison

        val eq_dec : K.t -> K.t -> bool
       end

      module TO :
       sig
        type t = K.t

        val compare : K.t -> K.t -> comparison

        val eq_dec : K.t -> K.t -> bool
       end
     end

    val eq_dec : K.t -> K.t -> bool

    val lt_dec : K.t -> K.t -> bool

    val eqb : K.t -> K.t -> bool
   end

  type forest =
  | Nil
  | Cons of K.t * forest * forest

  val forest_rect :
    'a1 -> (K.t -> forest -> 'a1 -> forest -> 'a1 -> 'a1) -> forest -> 'a1

  val forest_rec :
    'a1 -> (K.t -> forest -> 'a1 -> forest -> 'a1 -> 'a1) -> forest -> 'a1

  type t =
  | Empty
  | Root of forest

  val t_rect : 'a1 -> (forest -> 'a1) -> t -> 'a1

  val t_rec : 'a1 -> (forest -> 'a1) -> t -> 'a1

  val empty : t

  val containsf : forest -> K.t list -> bool

  val contains : t -> K.t list -> bool

  val singletonf : K.t list -> forest

  val addf : forest -> K.t list -> forest

  val add : t -> K.t list -> t

  val singleton : K.t list -> t
 end
