open Atom
open Datatypes
open Lclauses
open Lit
open Mcnf
open Nnf

type t = Lclauses.t list

val from_n_nnf : int -> Nnf.t -> int -> Mcnf.t * int

val from_nnf_with_sur : int -> Nnf.t -> int -> Mcnf.t

val from_nnf : Nnf.t -> Mcnf.t
