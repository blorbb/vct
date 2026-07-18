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

val first_ctx : Mcnf0.t -> Lclauses.t

val first_cpls : Mcnf0.t -> CplClause.t list

val first_boxes : Mcnf0.t -> BoxClause.t list

val next_ctx : Mcnf0.t -> Lclauses.t list

val with_first_cpls :
  Mcnf0.t -> (CplClause.t list -> CplClause.t list) -> Lclauses.t list

val add_conflict_set : Mcnf0.t -> int list -> Lclauses.t list

val cplsolver_mcnf : Mcnf0.t -> CplSolver.t

val conflict_set_of : Mcnf0.t -> t -> int -> Lit.t list -> int list
