open Assumptions
open Basics
open Cnf
open CplClause
open List
open ListDef
open Lit
open Solution

type t = Bindings.t

(** val make : unit -> t **)

let make = Bindings.make

(** val add_clause : t -> CplClause.t -> t **)

let add_clause = Bindings.add_clause

(** val solve_with_assumptions : t -> Assumptions.t -> Solution.t **)

let solve_with_assumptions = Bindings.solve_with_assumptions

(** val make_with_clauses : Cnf.t -> t **)

let make_with_clauses clauses =
  fold_right (flip add_clause) (make ()) clauses

(** val add_conflict_set : t -> int list -> t **)

let add_conflict_set s cs =
  add_clause s (map (fun x -> Neg x) cs)
