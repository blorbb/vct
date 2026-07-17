open Assumptions
open Basics
open Cnf
open CplClause
open CplSolution
open List
open ListDef
open Lit

type t = Bindings.t

val make : unit -> t

val add_clause : t -> CplClause.t -> t

val solve_with_assumptions : t -> Assumptions.t -> CplSolution.t

val make_with_clauses : Cnf.t -> t

val add_conflict_set : t -> int list -> t
