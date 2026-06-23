open Assumptions
open DiaClause
open Valuation

type t =
| Id of Assumptions.t
| JumpRestart of Valuation.t * DiaClause.t * t * t
