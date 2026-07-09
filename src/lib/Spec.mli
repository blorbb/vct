open Assumptions
open CplSolution
open CplSolver
open Datatypes
open Derivation
open DiaClause
open Fml
open ImportStd
open Lclauses
open List
open ListDef
open Logic
open Mcnf0
open McnfExt
open Nnf
open Tree
open Valuation

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

  val is_sat : t -> bool
 end

val tableau_jumps :
  t -> Lclauses.t -> Mcnf0.t -> (Assumptions.t -> Solution.t) ->
  JumpSolution.t

val tableau : Assumptions.t -> CplSolver.t -> Mcnf0.t -> Solution.t

val solve_mcnf : Mcnf0.t -> Solution.t

val solve_fml : Fml.t -> Solution.t
