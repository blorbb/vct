open BoxClause
open CplClause
open Datatypes
open ImportStd
open Lclauses
open List
open ListDef
open Lit
open Mcnf0
open Valuation

(** val first_ctx : Mcnf0.t -> Lclauses.t **)

let first_ctx = function
| [] -> empty
| l0 :: _ -> l0

(** val first_cpls : Mcnf0.t -> CplClause.t list **)

let first_cpls mc0 =
  (first_ctx mc0).cpls

(** val first_boxes : Mcnf0.t -> BoxClause.t list **)

let first_boxes mc0 =
  (first_ctx mc0).boxes

(** val next_ctx : Mcnf0.t -> Lclauses.t list **)

let next_ctx = function
| [] -> []
| _ :: mc1 -> mc1

(** val with_first_cpls :
    Mcnf0.t -> (CplClause.t list -> CplClause.t list) -> Lclauses.t list **)

let with_first_cpls mc0 f =
  let l0 = first_ctx mc0 in
  let mc1 = next_ctx mc0 in
  { cpls = (f l0.cpls); boxes = l0.boxes; dias = l0.dias } :: mc1

(** val add_conflict_set : Mcnf0.t -> int list -> Lclauses.t list **)

let add_conflict_set mc0 cs =
  with_first_cpls mc0 (fun x -> (map (fun x0 -> Neg x0) cs) :: x)

(** val conflict_set_of : Mcnf0.t -> t -> int -> Lit.t list -> int list **)

let conflict_set_of mc0 v dia_antecedent core =
  apply
    (apply
      (apply
        (apply (first_boxes mc0) (filter (fun box -> forces_atm v (fst box))))
        (filter (fun box -> existsb (eqb (snd box)) core)))
      (map fst))
    (fun x -> dia_antecedent :: x)
