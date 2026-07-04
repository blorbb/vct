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

(** val max_atm : t -> int **)

let max_atm phi =
  list_max_nat (map max_atm phi)

(** val from_mclause : Mclause.t -> t **)

let rec from_mclause = function
| Cpl cpl -> { cpls = (cpl :: []); boxes = []; dias = [] } :: []
| Box box -> { cpls = []; boxes = (box :: []); dias = [] } :: []
| Dia dia -> { cpls = []; boxes = []; dias = (dia :: []) } :: []
| Ctx ctx -> empty :: (from_mclause ctx)

(** val zip_merge : t -> t -> t **)

let rec zip_merge a b =
  match a with
  | [] -> (match b with
           | [] -> a
           | _ :: _ -> b)
  | ha :: ta ->
    (match b with
     | [] -> a
     | hb :: tb -> (merge ha hb) :: (zip_merge ta tb))

(** val from_mcnf : Mcnf0.t -> t **)

let rec from_mcnf = function
| [] -> []
| head :: tail -> zip_merge (from_mclause head) (from_mcnf tail)

module ClauseOrd1 =
 struct
  type t = BoxClause.t

  (** val leb : t -> t -> bool **)

  let leb x y =
    leb (fst x) (fst y)
 end

module ClauseOrd2 =
 struct
  type t = BoxClause.t

  (** val leb : t -> t -> bool **)

  let leb x y =
    Lit.leb (snd x) (snd y)
 end

module ClauseSort1 = Sort(ClauseOrd1)

module ClauseSort2 = Sort(ClauseOrd2)

(** val group_by : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list list **)

let rec group_by r = function
| [] -> []
| x :: xs ->
  (match group_by r xs with
   | [] -> (x :: []) :: []
   | g :: gs ->
     (match g with
      | [] -> (x :: []) :: gs
      | y :: _ -> if r x y then (x :: g) :: gs else (x :: []) :: (g :: gs)))

(** val rhs_opt :
    BoxClause.t list -> int -> (BoxClause.t * CplClause.t list) * int **)

let rhs_opt group sur =
  match group with
  | [] -> (((0, (Pos 0)), []), sur)
  | cl :: l ->
    let (_, b) = cl in
    (match l with
     | [] -> ((cl, []), sur)
     | _ :: _ ->
       (((sur, b),
         (map (fun pat -> let (a, _) = pat in (Neg a) :: ((Pos sur) :: []))
           group)),
         (Stdlib.Int.succ sur)))

(** val lhs_opt :
    BoxClause.t list -> int -> (BoxClause.t * CplClause.t list) * int **)

let lhs_opt group sur =
  match group with
  | [] -> (((0, (Pos 0)), []), sur)
  | cl :: l ->
    let (a, _) = cl in
    (match l with
     | [] -> ((cl, []), sur)
     | _ :: _ ->
       (((a, (Pos sur)),
         (map (fun pat -> let (_, b) = pat in (Neg sur) :: (b :: [])) group)),
         (Stdlib.Int.succ sur)))

(** val opt_on_groups :
    (BoxClause.t list -> int -> (BoxClause.t * CplClause.t list) * int) ->
    BoxClause.t list list -> int -> (BoxClause.t list * CplClause.t
    list) * int **)

let opt_on_groups opt groups sur =
  fold_left (fun pat group ->
    let (y, sur0) = pat in
    let (new_clauses, cpls0) = y in
    let (p, sur1) = opt group sur0 in
    let (new_clause, new_cpls) = p in
    (((new_clause :: new_clauses), (app new_cpls cpls0)), sur1)) groups (([],
    []), sur)

(** val simplify_eq_rhs :
    BoxClause.t list -> int -> (BoxClause.t list * CplClause.t list) * int **)

let simplify_eq_rhs clauses sur =
  let sorted = ClauseSort2.sort clauses in
  let grouped = group_by (fun a b -> Lit.eqb (snd a) (snd b)) sorted in
  opt_on_groups rhs_opt grouped sur

(** val simplify_eq_lhs :
    BoxClause.t list -> int -> (BoxClause.t list * CplClause.t list) * int **)

let simplify_eq_lhs clauses sur =
  let sorted = ClauseSort1.sort clauses in
  let grouped = group_by (fun a b -> eqb (fst a) (fst b)) sorted in
  opt_on_groups lhs_opt grouped sur

(** val simplify_sur : t -> int -> Lclauses.t list **)

let rec simplify_sur mc0 sur =
  match mc0 with
  | [] -> []
  | t0 :: mc1 ->
    let { cpls = cpls0; boxes = boxes0; dias = dias0 } = t0 in
    let (p, sur1) = simplify_eq_lhs boxes0 sur in
    let (boxes_lhs_opt, cpls_mc1) = p in
    let (p0, sur2) = simplify_eq_rhs boxes_lhs_opt sur1 in
    let (boxes_rhs_opt, cpls_box) = p0 in
    let (p1, sur3) = simplify_eq_rhs dias0 sur2 in
    let (dias_rhs_opt, cpls_dia) = p1 in
    let mc1' = simplify_sur mc1 sur3 in
    { cpls = (app cpls_box (app cpls_dia cpls0)); boxes = boxes_rhs_opt;
    dias = dias_rhs_opt } :: (zip_merge ((make_cpls cpls_mc1) :: []) mc1')

(** val simplify : t -> Lclauses.t list **)

let simplify mc0 =
  simplify_sur mc0 (add (Stdlib.Int.succ 0) (max_atm mc0))
