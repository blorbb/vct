open Datatypes

(** val eqb : int -> int -> bool **)

let eqb = Stdlib.Int.equal

(** val succ : int -> int **)

let succ = Stdlib.Int.succ

(** val max : int -> int -> int **)

let max = Stdlib.Int.max

(** val compare : int -> int -> comparison **)

let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

(** val eq_dec : int -> int -> bool **)

let eq_dec = Stdlib.Int.equal
