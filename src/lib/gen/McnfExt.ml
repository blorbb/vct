open BoxClause
open CplClause
open CplSolver
open Datatypes
open Lclauses
open List
open ListDef
open Lit
open Mcnf0
open Valuation

(** val first_cpls : Mcnf0.t -> CplClause.t list **)

let first_cpls mc0 =
  (first_ctx mc0).cpls

(** val first_boxes : Mcnf0.t -> BoxClause.t list **)

let first_boxes mc0 =
  (first_ctx mc0).boxes

(** val cplsolver_mcnf : Mcnf0.t -> CplSolver.t **)

let cplsolver_mcnf mc0 =
  make_with_clauses (first_cpls mc0)

(** val conflict_set_of : Mcnf0.t -> t -> int -> Lit.t list -> int list **)

let conflict_set_of mc0 v dia_antecedent core =
  dia_antecedent :: (map fst
                      (filter (fun box -> existsb (eqb (snd box)) core)
                        (filter (fun box -> forces_atm v (fst box))
                          (first_boxes mc0))))
