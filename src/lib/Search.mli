open Assumptions
open Derivation
open DiaClause
open Tree

module JumpSolution :
 sig
  type t =
  | Sat of Tree.t list
  | Unsat of DiaClause.t * Assumptions.t * Derivation.t

  val t_rect :
    (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Derivation.t ->
    'a1) -> t -> 'a1

  val t_rec :
    (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Derivation.t ->
    'a1) -> t -> 'a1
 end

module Solution :
 sig
  type t =
  | Sat of Tree.t
  | Unsat of Assumptions.t * Derivation.t

  val t_rect :
    (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1

  val t_rec :
    (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1
 end
