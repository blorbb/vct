(** Equisatisfiable conversion from NNF to MCNF.

    We use the term 'surrogate' to mean an unused atom value. *)

From CegarTableaux Require Lit Nnf Kripke Lclauses Mcnf.Mcnf.
From CegarTableaux Require Import ImportStd.


(** Merge two [Mcnf.t]'s together.

    This will retain all elements, and output a list the length of
    the longer list. *)
Fixpoint zip_merge (a b : Mcnf.t) : Mcnf.t :=
  match a, b with
  | ha::ta, hb::tb => Lclauses.merge ha hb :: zip_merge ta tb
  | a, [] => a
  | [], b => b
  end.


(** Converts [n -> phi] to MCNF, with a given surrogate value [k].

    Returns a pair of the MCNF formula, and the next free surrogate.

    Corresponds to [mcnf(n -> phi, k)] in the paper. *)
Fixpoint from_n_nnf (n : nat) (phi : Nnf.t) (k : nat) : (Mcnf.t * nat) :=
  match phi with
  (* n -> l  =>  ~n \/ l *)
  | Nnf.Lit l =>
    (
      [Lclauses.make_cpls [[Lit.Neg n ; l]]],
      k
    )
  (* n -> A /\ B  =>  n -> A ; n -> B *)
  | Nnf.And A B =>
    let (A_mcnf, k) := from_n_nnf n A k in
    let (B_mcnf, k) := from_n_nnf n B k in
    (
      zip_merge A_mcnf B_mcnf,
      k
    )
  (* n -> A \/ B  =>  n -> nA \/ nB ; nA -> A ; nB -> B *)
  | Nnf.Or A B =>
    let (nA, k) := (k, S k) in
    let (nB, k) := (k, S k) in
    let (A_mcnf, k) := from_n_nnf nA A k in
    let (B_mcnf, k) := from_n_nnf nB B k in
    (
      zip_merge [Lclauses.make_cpls [[Lit.Neg n ; Lit.Pos nA ; Lit.Pos nB]]]
        (zip_merge A_mcnf B_mcnf),
      k
    )
  (* n -> []A  =>  n -> []nA ; [](nA -> A) *)
  | Nnf.Box A =>
    let (nA, k) := (k, S k) in
    let (A_mcnf, k) := from_n_nnf nA A k in
    (
      Lclauses.make [] [(n, Lit.Pos nA)] [] :: A_mcnf,
      k
    )
  (* n -> <>A  =>  n -> <>nA ; [](nA -> A) *)
  | Nnf.Dia A =>
    let (nA, k) := (k, S k) in
    let (A_mcnf, k) := from_n_nnf nA A k in
    (
      Lclauses.make [] [] [(n, Lit.Pos nA)] :: A_mcnf,
      k
    )
  end.


(** Converts [phi] with a name and surrogate to [n /\ mcnf(n -> phi, k)]. *)
Definition from_nnf_with_sur (n : nat) (phi : Nnf.t) (k : nat) : Mcnf.t :=
  zip_merge [Lclauses.make_cpls [[Lit.Pos n]]] (fst (from_n_nnf n phi k)).


(** Converts an NNF formula to MCNF. *)
Definition from_nnf (phi : Nnf.t) : Mcnf.t :=
  let n := S (Nnf.max_atm phi) in
  from_nnf_with_sur n phi (S n).
