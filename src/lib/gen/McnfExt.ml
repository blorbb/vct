open Assumptions
open CplSolver
open Datatypes
open List
open ListDef
open Lit
open Mcnf0
open Valuation

(** val box_culprits : Mcnf0.t -> t -> Assumptions.t -> int list **)

let box_culprits mc0 v core =
  map fst
    (filter (fun box -> existsb (eqb (snd box)) core)
      (filter (fun box -> forces_atm v (fst box)) (fst_boxes mc0)))

(** val cplsolver_mcnf : Mcnf0.t -> CplSolver.t **)

let cplsolver_mcnf mc0 =
  make_with_clauses (fst_cpls mc0)
