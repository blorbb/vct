open Assumptions
open CplSolver
open Datatypes
open List
open ListDef
open Lit
open Mcnf0
open Valuation

val box_culprits : Mcnf0.t -> t -> Assumptions.t -> int list

val cplsolver_mcnf : Mcnf0.t -> CplSolver.t
