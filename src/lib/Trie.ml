open Datatypes
open Orders

module Make =
 functor (K:UsualOrderedTypeFull) ->
 struct
  module K' =
   struct
    type t = K.t

    (** val compare : K.t -> K.t -> comparison **)

    let compare =
      K.compare

    (** val eq_dec : K.t -> K.t -> bool **)

    let eq_dec =
      K.eq_dec
   end

  module KFacts =
   struct
    module OrderTac =
     struct
      module OTF =
       struct
        type t = K.t

        (** val compare : K.t -> K.t -> comparison **)

        let compare =
          K.compare

        (** val eq_dec : K.t -> K.t -> bool **)

        let eq_dec =
          K'.eq_dec
       end

      module TO =
       struct
        type t = K.t

        (** val compare : K.t -> K.t -> comparison **)

        let compare =
          K.compare

        (** val eq_dec : K.t -> K.t -> bool **)

        let eq_dec =
          OTF.eq_dec
       end
     end

    (** val eq_dec : K.t -> K.t -> bool **)

    let eq_dec =
      K'.eq_dec

    (** val lt_dec : K.t -> K.t -> bool **)

    let lt_dec x y =
      let c = coq_CompSpec2Type x y (K.compare x y) in
      (match c with
       | CompLtT -> true
       | _ -> false)

    (** val eqb : K.t -> K.t -> bool **)

    let eqb x y =
      if eq_dec x y then true else false
   end

  type forest =
  | Nil
  | Cons of K.t * forest * forest

  (** val forest_rect :
      'a1 -> (K.t -> forest -> 'a1 -> forest -> 'a1 -> 'a1) -> forest -> 'a1 **)

  let rec forest_rect nil cons = function
  | Nil -> nil
  | Cons (key, child, next) ->
    cons key child (forest_rect nil cons child) next
      (forest_rect nil cons next)

  (** val forest_rec :
      'a1 -> (K.t -> forest -> 'a1 -> forest -> 'a1 -> 'a1) -> forest -> 'a1 **)

  let rec forest_rec nil cons = function
  | Nil -> nil
  | Cons (key, child, next) ->
    cons key child (forest_rec nil cons child) next (forest_rec nil cons next)

  type t =
  | Empty
  | Root of forest

  (** val t_rect : 'a1 -> (forest -> 'a1) -> t -> 'a1 **)

  let t_rect empty0 root = function
  | Empty -> empty0
  | Root f -> root f

  (** val t_rec : 'a1 -> (forest -> 'a1) -> t -> 'a1 **)

  let t_rec empty0 root = function
  | Empty -> empty0
  | Root f -> root f

  (** val empty : t **)

  let empty =
    Empty

  (** val containsf : forest -> K.t list -> bool **)

  let rec containsf f = function
  | [] -> true
  | kn :: ks' ->
    (match f with
     | Nil -> false
     | Cons (kt, child, next) ->
       (match K.compare kn kt with
        | Eq -> containsf child ks'
        | Lt -> false
        | Gt -> containsf next (kn :: ks')))

  (** val contains : t -> K.t list -> bool **)

  let contains trie ks =
    match trie with
    | Empty -> false
    | Root f -> containsf f ks

  (** val singletonf : K.t list -> forest **)

  let rec singletonf = function
  | [] -> Nil
  | kn :: ks' -> Cons (kn, (singletonf ks'), Nil)

  (** val addf : forest -> K.t list -> forest **)

  let rec addf f ks =
    match f with
    | Nil -> singletonf ks
    | Cons (kt, child, next) ->
      (match ks with
       | [] -> f
       | kn :: ks' ->
         (match K.compare kn kt with
          | Eq -> Cons (kt, (addf child ks'), next)
          | Lt -> Cons (kn, (singletonf ks'), f)
          | Gt -> Cons (kt, child, (addf next (kn :: ks')))))

  (** val add : t -> K.t list -> t **)

  let add trie ks =
    match trie with
    | Empty -> Root (singletonf ks)
    | Root f -> Root (addf f ks)

  (** val singleton : K.t list -> t **)

  let singleton =
    add Empty
 end
