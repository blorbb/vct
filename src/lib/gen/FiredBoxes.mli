open Assumptions
open Cached
open CplSolution
open CplSolver
open Datatypes
open Fml
open Lclauses
open List
open ListDef
open Lit
open Logic
open Mcnf0
open McnfExt
open Nnf
open NoModel
open Valuation

module Cache :
 sig
  module K' :
   sig
    type t = Lit.t

    val compare : Lit.t -> Lit.t -> comparison

    val eq_dec : Lit.t -> Lit.t -> bool
   end

  module KFacts :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = Lit.t

        val compare : Lit.t -> Lit.t -> comparison

        val eq_dec : Lit.t -> Lit.t -> bool
       end

      module TO :
       sig
        type t = Lit.t

        val compare : Lit.t -> Lit.t -> comparison

        val eq_dec : Lit.t -> Lit.t -> bool
       end
     end

    val eq_dec : Lit.t -> Lit.t -> bool

    val lt_dec : Lit.t -> Lit.t -> bool

    val eqb : Lit.t -> Lit.t -> bool
   end

  type forest = Cache.forest =
  | Nil
  | Cons of Lit.t * forest * forest

  val forest_rect :
    'a1 -> (Lit.t -> forest -> 'a1 -> forest -> 'a1 -> 'a1) -> forest -> 'a1

  val forest_rec :
    'a1 -> (Lit.t -> forest -> 'a1 -> forest -> 'a1 -> 'a1) -> forest -> 'a1

  type t = Cache.t =
  | Empty
  | Root of forest

  val t_rect : 'a1 -> (forest -> 'a1) -> t -> 'a1

  val t_rec : 'a1 -> (forest -> 'a1) -> t -> 'a1

  val empty : t

  val containsf : forest -> Lit.t list -> bool

  val contains : t -> Lit.t list -> bool

  val singletonf : Lit.t list -> forest

  val addf : forest -> Lit.t list -> forest

  val add : t -> Lit.t list -> t

  val singleton : Lit.t list -> t
 end

module Caches :
 sig
  type t = Cached.Cache.t list

  val contains : t -> Assumptions.t -> bool

  val destruct : t -> Cached.Cache.t * t

  val add : t -> Assumptions.t -> t
 end

module JumpSolution :
 sig
  type t = Cached.JumpSolution.t =
  | Sat of Cached.Caches.t
  | Unsat of int * Assumptions.t * Cached.Caches.t

  val t_rect :
    (Cached.Caches.t -> 'a1) -> (int -> Assumptions.t -> Cached.Caches.t ->
    'a1) -> t -> 'a1

  val t_rec :
    (Cached.Caches.t -> 'a1) -> (int -> Assumptions.t -> Cached.Caches.t ->
    'a1) -> t -> 'a1

  val get_caches : t -> Cached.Caches.t

  val without_caches : t -> JumpSolution.t
 end

module Solution :
 sig
  type t = Cached.Solution.t =
  | Sat of Cached.Caches.t
  | Unsat of Assumptions.t * Cached.Caches.t

  val t_rect :
    (Cached.Caches.t -> 'a1) -> (Assumptions.t -> Cached.Caches.t -> 'a1) ->
    t -> 'a1

  val t_rec :
    (Cached.Caches.t -> 'a1) -> (Assumptions.t -> Cached.Caches.t -> 'a1) ->
    t -> 'a1

  val is_sat : t -> bool

  val get_caches : t -> Cached.Caches.t

  val without_caches : t -> Solution.t
 end

val get_fired_boxes : t -> Lclauses.t -> Lit.t list

val tableau_jumps :
  t -> Lclauses.t -> Mcnf0.t -> (Assumptions.t -> Caches.t -> Solution.t) ->
  Lit.t list -> Caches.t -> JumpSolution.t

val tableau :
  Mcnf0.t -> CplSolver.t -> Assumptions.t -> Caches.t -> Solution.t

val solve_mcnf : Mcnf0.t -> Solution.t

val solve_fml : Fml.t -> Solution.t
