open Atom
open CplClause
open Datatypes
open Lclauses
open ListDef
open Lit
open Mcnf
open Nnf

type t = Lclauses.t list

val first_ctx : t -> Lclauses.t

val next_ctx : t -> Lclauses.t list

val with_first_cpls :
  t -> (CplClause.t list -> CplClause.t list) -> Lclauses.t list

val add_cs : t -> int list -> Lclauses.t list

val from_n_nnf : int -> Nnf.t -> int -> Mcnf.t * int

val from_nnf_with_sur : int -> Nnf.t -> int -> Mcnf.t

val from_nnf : Nnf.t -> Mcnf.t
