open Assumptions
open DiaClause
open Valuation

type t =
| Local of Assumptions.t
| JumpRestart of Valuation.t * DiaClause.t * t * t
