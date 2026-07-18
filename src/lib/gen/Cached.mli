open Assumptions
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
open Trie
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

  type forest =
  | Nil
  | Cons of Lit.t * forest * forest

  val forest_rect :
    'a1 -> (Lit.t -> forest -> 'a1 -> forest -> 'a1 -> 'a1) -> forest -> 'a1

  val forest_rec :
    'a1 -> (Lit.t -> forest -> 'a1 -> forest -> 'a1 -> 'a1) -> forest -> 'a1

  type t =
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
  type t = Cache.t list

  val contains : t -> Assumptions.t -> bool

  val destruct : t -> Cache.t * t

  val add : t -> Assumptions.t -> t
 end

module JumpSolution :
 sig
  type t =
  | Sat of Caches.t
  | Unsat of int * Assumptions.t * Caches.t
 end

module Solution :
 sig
  type t =
  | Sat of Caches.t
  | Unsat of Assumptions.t * Caches.t

  val is_sat : t -> bool
 end

val tableau_jumps :
  t -> Lclauses.t -> Mcnf0.t -> (Assumptions.t -> Caches.t -> Solution.t) ->
  Caches.t -> JumpSolution.t

val tableau :
  Mcnf0.t -> CplSolver.t -> Assumptions.t -> Caches.t -> Solution.t

val solve_mcnf : Mcnf0.t -> Solution.t

val solve_fml : Fml.t -> Solution.t
