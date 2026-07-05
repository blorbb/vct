open BoxClause
open CplClause
open Datatypes
open DiaClause

type t = { cpls : CplClause.t list; boxes : BoxClause.t list;
           dias : DiaClause.t list }

val empty : t

val make_cpls : CplClause.t list -> t

val merge : t -> t -> t
