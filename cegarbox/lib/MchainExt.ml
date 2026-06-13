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

(** val first_ctx : Mchain.t -> Lclauses.t **)

let first_ctx = function
| [] -> empty
| l0 :: _ -> l0

(** val first_cpls : Mchain.t -> CplClause.t list **)

let first_cpls mc0 =
  (first_ctx mc0).cpls

(** val first_boxes : Mchain.t -> BoxClause.t list **)

let first_boxes mc0 =
  (first_ctx mc0).boxes

(** val next_ctx : Mchain.t -> Lclauses.t list **)

let next_ctx = function
| [] -> []
| _ :: mc1 -> mc1

(** val with_first_cpls :
    Mchain.t -> (CplClause.t list -> CplClause.t list) -> Lclauses.t list **)

let with_first_cpls mc0 f =
  let l0 = first_ctx mc0 in
  let mc1 = next_ctx mc0 in
  { cpls = (f l0.cpls); boxes = l0.boxes; dias = l0.dias } :: mc1

(** val add_conflict_set : Mchain.t -> int list -> Lclauses.t list **)

let add_conflict_set mc0 cs =
  with_first_cpls mc0 (fun x -> (map (fun x0 -> Neg x0) cs) :: x)

(** val conflict_set_of : Mchain.t -> t -> int -> Lit.t list -> int list **)

let conflict_set_of mc0 v dia_antecedent core =
  apply
    (apply
      (apply
        (apply (first_boxes mc0) (filter (fun box -> forces_atm v (fst box))))
        (filter (fun box -> existsb (eqb (snd box)) core)))
      (map fst))
    (fun x -> dia_antecedent :: x)
