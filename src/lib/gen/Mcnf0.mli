open Atom
open BoxClause
open CplClause
open Datatypes
open Lclauses
open ListDef
open Lit
open Mcnf
open Nnf

type t = Lclauses.t list

val fst_mc : t -> Lclauses.t

val next_mc : t -> Lclauses.t list

val fst_cpls : t -> CplClause.t list

val fst_boxes : t -> BoxClause.t list

val with_fst_cpls :
  t -> (CplClause.t list -> CplClause.t list) -> Lclauses.t list

val add_cs : t -> int list -> Lclauses.t list

val from_n_nnf : int -> Nnf.t -> int -> Mcnf.t * int

val from_nnf_with_sur : int -> Nnf.t -> int -> Mcnf.t

val from_nnf : Nnf.t -> Mcnf.t
