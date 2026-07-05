open Datatypes
open Lclauses
open Lit
open Mcnf
open Nnf

type t = Lclauses.t list

(** val from_n_nnf : int -> Nnf.t -> int -> Mcnf.t * int **)

let rec from_n_nnf n phi k =
  match phi with
  | Lit l -> (((make_cpls (((Neg n) :: (l :: [])) :: [])) :: []), k)
  | And (a, b) ->
    let (a_mcnf, k0) = from_n_nnf n a k in
    let (b_mcnf, k1) = from_n_nnf n b k0 in ((zip_merge a_mcnf b_mcnf), k1)
  | Or (a, b) ->
    let k0 = Stdlib.Int.succ k in
    let k1 = Stdlib.Int.succ k0 in
    let (a_mcnf, k2) = from_n_nnf k a k1 in
    let (b_mcnf, k3) = from_n_nnf k0 b k2 in
    ((zip_merge
       ((make_cpls (((Neg n) :: ((Pos k) :: ((Pos k0) :: []))) :: [])) :: [])
       (zip_merge a_mcnf b_mcnf)),
    k3)
  | Box a ->
    let k0 = Stdlib.Int.succ k in
    let (a_mcnf, k1) = from_n_nnf k a k0 in
    (({ cpls = []; boxes = ((n, (Pos k)) :: []); dias = [] } :: a_mcnf), k1)
  | Dia a ->
    let k0 = Stdlib.Int.succ k in
    let (a_mcnf, k1) = from_n_nnf k a k0 in
    (({ cpls = []; boxes = []; dias = ((n, (Pos k)) :: []) } :: a_mcnf), k1)

(** val from_nnf_with_sur : int -> Nnf.t -> int -> Mcnf.t **)

let from_nnf_with_sur n phi k =
  zip_merge ((make_cpls (((Pos n) :: []) :: [])) :: [])
    (fst (from_n_nnf n phi k))

(** val from_nnf : Nnf.t -> Mcnf.t **)

let from_nnf phi =
  let n = Stdlib.Int.succ (max_atm phi) in
  from_nnf_with_sur n phi (Stdlib.Int.succ n)
