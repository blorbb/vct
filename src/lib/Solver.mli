open Assumptions
open CplSolver
open Datatypes
open Derivation
open DiaClause
open Fml
open Lclauses
open List
open ListDef
open Logic
open Mchain
open MchainExt
open Mcnf0
open Nnf
open Solution
open Tree
open Utils
open Valuation

module JumpSolution :
 sig
  type t = Search.JumpSolution.t =
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
  type t = Search.Solution.t =
  | Sat of Tree.t
  | Unsat of Assumptions.t * Derivation.t

  val t_rect :
    (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1

  val t_rec :
    (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1
 end

val tableau_jumps :
  t -> Lclauses.t -> Mchain.t -> Tree.t list -> (Assumptions.t -> Solution.t)
  -> JumpSolution.t

val tableau : Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t

val solve_mchain : Mchain.t -> Solution.t

val solve_fml : Fml.t -> Solution.t
