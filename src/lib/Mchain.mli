open BoxClause
open CplClause
open Datatypes
open Lclauses
open List
open ListDef
open ListExt
open Lit
open Mclause
open Mcnf0
open Mergesort
open Nat

type t = Lclauses.t list

val max_atm : t -> int

val from_mclause : Mclause.t -> t

val zip_merge : t -> t -> t

val from_mcnf : Mcnf0.t -> t

module ClauseOrd1 :
 sig
  type t = BoxClause.t

  val leb : t -> t -> bool
 end

module ClauseOrd2 :
 sig
  type t = BoxClause.t

  val leb : t -> t -> bool
 end

module ClauseSort1 :
 sig
  val merge : BoxClause.t list -> BoxClause.t list -> BoxClause.t list

  val merge_list_to_stack :
    BoxClause.t list option list -> BoxClause.t list -> BoxClause.t list
    option list

  val merge_stack : BoxClause.t list option list -> BoxClause.t list

  val iter_merge :
    BoxClause.t list option list -> BoxClause.t list -> BoxClause.t list

  val sort : BoxClause.t list -> BoxClause.t list

  val flatten_stack : BoxClause.t list option list -> BoxClause.t list
 end

module ClauseSort2 :
 sig
  val merge : BoxClause.t list -> BoxClause.t list -> BoxClause.t list

  val merge_list_to_stack :
    BoxClause.t list option list -> BoxClause.t list -> BoxClause.t list
    option list

  val merge_stack : BoxClause.t list option list -> BoxClause.t list

  val iter_merge :
    BoxClause.t list option list -> BoxClause.t list -> BoxClause.t list

  val sort : BoxClause.t list -> BoxClause.t list

  val flatten_stack : BoxClause.t list option list -> BoxClause.t list
 end

val group_by : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list list

val rhs_opt :
  BoxClause.t list -> int -> (BoxClause.t * CplClause.t list) * int

val lhs_opt :
  BoxClause.t list -> int -> (BoxClause.t * CplClause.t list) * int

val opt_on_groups :
  (BoxClause.t list -> int -> (BoxClause.t * CplClause.t list) * int) ->
  BoxClause.t list list -> int -> (BoxClause.t list * CplClause.t list) * int

val simplify_eq_rhs :
  BoxClause.t list -> int -> (BoxClause.t list * CplClause.t list) * int

val simplify_eq_lhs :
  BoxClause.t list -> int -> (BoxClause.t list * CplClause.t list) * int

val simplify_sur : t -> int -> Lclauses.t list

val simplify : t -> Lclauses.t list
