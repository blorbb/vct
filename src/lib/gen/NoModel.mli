open Assumptions
open CplSolution
open CplSolver
open Datatypes
open Fml
open Lclauses
open List
open ListDef
open Logic
open Mcnf0
open McnfExt
open Nnf
open Valuation

module JumpSolution :
 sig
  type t =
  | Sat
  | Unsat of int * Assumptions.t
 end

module Solution :
 sig
  type t =
  | Sat
  | Unsat of Assumptions.t

  val is_sat : t -> bool
 end

val tableau_jumps :
  t -> Lclauses.t -> Mcnf0.t -> (Assumptions.t -> Solution.t) ->
  JumpSolution.t

val tableau : Mcnf0.t -> CplSolver.t -> Assumptions.t -> Solution.t

val solve_mcnf : Mcnf0.t -> Solution.t

val solve_fml : Fml.t -> Solution.t
