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

(** val fst_mc : t -> Lclauses.t **)

let fst_mc = function
| [] -> empty
| l0 :: _ -> l0

(** val next_mc : t -> Lclauses.t list **)

let next_mc = function
| [] -> []
| _ :: mc1 -> mc1

(** val fst_cpls : t -> CplClause.t list **)

let fst_cpls mc0 =
  (fst_mc mc0).cpls

(** val fst_boxes : t -> BoxClause.t list **)

let fst_boxes mc0 =
  (fst_mc mc0).boxes

(** val with_fst_cpls :
    t -> (CplClause.t list -> CplClause.t list) -> Lclauses.t list **)

let with_fst_cpls mc0 f =
  let l0 = fst_mc mc0 in
  let mc1 = next_mc mc0 in
  { cpls = (f l0.cpls); boxes = l0.boxes; dias = l0.dias } :: mc1

(** val add_cs : t -> int list -> Lclauses.t list **)

let add_cs mc0 cs =
  with_fst_cpls mc0 (fun x -> (map (fun x0 -> Neg x0) cs) :: x)

(** val from_n_nnf : int -> Nnf.t -> int -> Mcnf.t * int **)

let rec from_n_nnf n phi k =
  match phi with
  | Lit l -> (((make_cpls (((Neg n) :: (l :: [])) :: [])) :: []), k)
  | And (a, b) ->
    let (a_mcnf, k0) = from_n_nnf n a k in
    let (b_mcnf, k1) = from_n_nnf n b k0 in ((zip_merge a_mcnf b_mcnf), k1)
  | Or (a, b) ->
    (match a with
     | Lit al ->
       (match b with
        | Lit bl ->
          (((make_cpls (((Neg n) :: (al :: (bl :: []))) :: [])) :: []), k)
        | _ ->
          let k0 = succ k in
          let k1 = succ k0 in
          let (a_mcnf, k2) = from_n_nnf k a k1 in
          let (b_mcnf, k3) = from_n_nnf k0 b k2 in
          ((zip_merge
             ((make_cpls (((Neg n) :: ((Pos k) :: ((Pos k0) :: []))) :: [])) :: [])
             (zip_merge a_mcnf b_mcnf)),
          k3))
     | _ ->
       let k0 = succ k in
       let k1 = succ k0 in
       let (a_mcnf, k2) = from_n_nnf k a k1 in
       let (b_mcnf, k3) = from_n_nnf k0 b k2 in
       ((zip_merge
          ((make_cpls (((Neg n) :: ((Pos k) :: ((Pos k0) :: []))) :: [])) :: [])
          (zip_merge a_mcnf b_mcnf)),
       k3))
  | Box a ->
    (match a with
     | Lit l -> (({ cpls = []; boxes = ((n, l) :: []); dias = [] } :: []), k)
     | _ ->
       let k0 = succ k in
       let (a_mcnf, k1) = from_n_nnf k a k0 in
       (({ cpls = []; boxes = ((n, (Pos k)) :: []); dias = [] } :: a_mcnf),
       k1))
  | Dia a ->
    (match a with
     | Lit l -> (({ cpls = []; boxes = []; dias = ((n, l) :: []) } :: []), k)
     | _ ->
       let k0 = succ k in
       let (a_mcnf, k1) = from_n_nnf k a k0 in
       (({ cpls = []; boxes = []; dias = ((n, (Pos k)) :: []) } :: a_mcnf),
       k1))

(** val from_nnf_with_sur : int -> Nnf.t -> int -> Mcnf.t **)

let from_nnf_with_sur n phi k =
  zip_merge ((make_cpls (((Pos n) :: []) :: [])) :: [])
    (fst (from_n_nnf n phi k))

(** val from_nnf : Nnf.t -> Mcnf.t **)

let from_nnf phi =
  let n = succ (max_atm phi) in from_nnf_with_sur n phi (succ n)
