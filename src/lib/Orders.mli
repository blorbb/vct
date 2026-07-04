
module type TotalLeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end
