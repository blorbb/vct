open BoxClause
open CplClause
open Datatypes
open DiaClause
open ListDef
open ListExt
open PeanoNat
open Utils

type t = { cpls : CplClause.t list; boxes : BoxClause.t list;
           dias : DiaClause.t list }

(** val empty : t **)

let empty =
  { cpls = []; boxes = []; dias = [] }

(** val make_cpls : CplClause.t list -> t **)

let make_cpls cpls0 =
  { cpls = cpls0; boxes = []; dias = [] }

(** val merge : t -> t -> t **)

let merge a b =
  { cpls = (app a.cpls b.cpls); boxes = (app a.boxes b.boxes); dias =
    (app a.dias b.dias) }

(** val max_atm : t -> int **)

let max_atm phi =
  Nat.max (apply (apply phi.cpls (map CplClause.max_atm)) list_max_nat)
    (Nat.max (apply (apply phi.boxes (map BoxClause.max_atm)) list_max_nat)
      (apply (apply phi.dias (map max_atm)) list_max_nat))
