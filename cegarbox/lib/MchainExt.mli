open BoxClause
open CplClause
open Datatypes
open Lclauses
open List
open ListDef
open Lit
open Mchain
open Utils
open Valuation

val first_ctx : Mchain.t -> Lclauses.t

val first_cpls : Mchain.t -> CplClause.t list

val first_boxes : Mchain.t -> BoxClause.t list

val next_ctx : Mchain.t -> Lclauses.t list

val with_first_cpls :
  Mchain.t -> (CplClause.t list -> CplClause.t list) -> Lclauses.t list

val add_conflict_set : Mchain.t -> int list -> Lclauses.t list

val conflict_set_of : Mchain.t -> t -> int -> Lit.t list -> int list
