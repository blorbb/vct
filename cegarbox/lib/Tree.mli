open Valuation

type t =
| Coq_make of Valuation.t * t list
