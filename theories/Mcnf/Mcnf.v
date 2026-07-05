(** MCNF type with basic lemmas and definitions *)

From CegarTableaux Require Lit Nnf Kripke Lclauses.
From CegarTableaux Require Import ImportStd.


(** An MCNF formula, a list of clauses, where the 'local' clauses at the head
    are clauses that need to be satisfied at the 'current' world, and the tail
    is one modal context away. *)
Definition t := list Lclauses.t.


Fixpoint force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  match phi with
  | [] => True
  | head :: tail => Lclauses.force M w0 head /\
    forall w1, R w0 w1 -> force M w1 tail
  end.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.


Definition unsatisfiable (phi : t) : Prop :=
  ~ satisfiable phi.


Definition atm_in (p : nat) (phi : t) : Prop := List.Exists (Lclauses.atm_in p) phi.

Arguments atm_in p phi /.


Lemma atm_in_cons : forall p l0 mc1, Mcnf.atm_in p (l0::mc1) <-> Lclauses.atm_in p l0 \/ Mcnf.atm_in p mc1.
Proof. intros. cbn. rewrite Exists_cons. reflexivity. Qed.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w0 : W) (p : nat), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).


Lemma agree_cons : forall {W} {R} {M M' : @Kripke.t W R} l0 mc1,
  agree (l0::mc1) M M' <-> Lclauses.agree l0 M M' /\ agree mc1 M M'.
Proof with try easy; auto with datatypes ct.
  intros *. unfold agree, Lclauses.agree. split.
  - intros Hagree. split.
    + intros w0 p Hp_in_l0. rewrite Hagree... unfold atm_in...
    + intros w0 p Hp_in_mc1. rewrite Hagree... unfold atm_in...
  - intros [Hl0_agree Hmc1_agree] w0 p Hp_in.
    unfold atm_in in Hp_in. rewrite List.Exists_exists in Hp_in.
    destruct Hp_in as [ln [[Hln_l0 | Hln_in_mc1] Hp_in_ln]].
    + subst ln. rewrite Hl0_agree...
    + rewrite Hmc1_agree...
      unfold atm_in. rewrite List.Exists_exists. exists ln...
Qed.


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with try easy; auto with datatypes.
  intros W R M M' phi w0 Hagree. revert w0.

  induction phi as [|l0 mc1 IHphi]; intros w0; try tauto.
  apply agree_cons in Hagree as [Hagree_l0 Hagree_mc1].
  forward IHphi by exact Hagree_mc1.
  cbn [force].
  rewrite (Lclauses.meaningful_valuations M M')...
  setoid_rewrite IHphi...
Qed.


Definition max_atm (phi : t) : nat :=
  list_max_nat (List.map Lclauses.max_atm phi).


Lemma atm_le_max : forall (phi : t) (p : nat),
  atm_in p phi -> p <= (max_atm phi).
Proof with try easy.
  intros phi p Hatm.
  unfold atm_in in Hatm. rewrite List.Exists_exists in Hatm.
  destruct Hatm as [lclause [Hlclause_in Hp_lclauses]].
  apply Lclauses.atm_le_max in Hp_lclauses.
  apply nat_le_mapped_list_max with (a := lclause)...
Qed.


(** Merge two [t]'s together.

    This will retain all elements, and output a list the length of
    the longer list. *)
Fixpoint zip_merge (a b : t) : t :=
  match a, b with
  | ha::ta, hb::tb => Lclauses.merge ha hb :: zip_merge ta tb
  | a, [] => a
  | [], b => b
  end.


Lemma force_zip_merge_and : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (A B : t),
  force M w0 (zip_merge A B) <-> force M w0 A /\ force M w0 B.
Proof.
  intros W R M w0 A. revert w0.

  (* induction on A, case-by-case on arbitrary B *)
  induction A as [|ha ta IHta]; intros w0 B; destruct B as [| hb tb].
  (* trivial empty cases *)
  - cbn. tauto.
  - cbn. tauto.
  - cbn. tauto.
  (* merge (ha::ta) (hb::tb) <-> (ha::ta) and (hb::tb) *)
  - cbn [zip_merge force].
    rewrite Lclauses.force_merge_and.
    setoid_rewrite IHta.
    intuition (auto with solve_subterm).
Qed.


Lemma in_zip_merge_or :
  forall (A B : t) (p : nat),
  atm_in p (zip_merge A B) <-> atm_in p A \/ atm_in p B.
Proof.
  intros A B p. revert B.
  induction A as [| Al0 Amc1 IH]; intro B; destruct B as [|Bl0 Bmc1].
  - cbn. autorewrite with list. tauto.
  - cbn. autorewrite with list. tauto.
  - cbn. autorewrite with list. tauto.
  - cbn [zip_merge] in *.
    repeat rewrite atm_in_cons. rewrite Lclauses.in_merge_or.
    rewrite IH. tauto.
Qed.
