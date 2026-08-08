(** MCNF type with basic lemmas and definitions *)

From Vct Require Lit Nnf Kripke Lclauses.
From Vct Require Import ImportStd.


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

Definition atm_in (p : Atom.t) (phi : t) : Prop :=
  List.Exists (Lclauses.atm_in p) phi.
Arguments atm_in : simpl never.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.

Definition unsatisfiable (phi : t) : Prop :=
  ~ satisfiable phi.

Definition satisfiable_kt (phi : t) : Prop :=
  exists W R `(Reflexive W R) (M : @Kripke.t W R) (w0 : W), force M w0 phi.

Definition unsatisfiable_kt (phi : t) : Prop :=
  ~ satisfiable_kt phi.


Lemma atm_in_nil : forall p, Mcnf.atm_in p [] <-> False.
Proof. intros. unfold atm_in. now rewrite List.Exists_nil. Qed.
Global Hint Rewrite atm_in_nil : ct.
Lemma atm_in_cons : forall p l0 mc1, Mcnf.atm_in p (l0::mc1) <-> Lclauses.atm_in p l0 \/ Mcnf.atm_in p mc1.
Proof. intros. unfold atm_in. now rewrite Exists_cons. Qed.
Global Hint Rewrite atm_in_cons : ct.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w0 : W) (p : Atom.t), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).


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


Definition max_atm (phi : t) : Atom.t :=
  Atom.list_max (List.map Lclauses.max_atm phi).


Lemma atm_le_max : forall (phi : t) (p : Atom.t),
  atm_in p phi -> p <= (max_atm phi).
Proof with try easy.
  intros phi p Hatm.
  unfold atm_in in Hatm. rewrite List.Exists_exists in Hatm.
  destruct Hatm as [lclause [Hlclause_in Hp_lclauses]].
  apply Lclauses.atm_le_max in Hp_lclauses.
  apply Atom.le_mapped_list_max with (a := lclause)...
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
Global Hint Rewrite @force_zip_merge_and : ct.

Lemma in_zip_merge_or :
  forall (A B : t) (p : Atom.t),
  atm_in p (zip_merge A B) <-> atm_in p A \/ atm_in p B.
Proof.
  intros A B p. revert B.
  induction A as [| Al0 Amc1 IH]; intro B; destruct B as [|Bl0 Bmc1].
  - cbn. now autorewrite with list ct prop.
  - cbn. now autorewrite with list ct prop.
  - cbn. now autorewrite with list ct prop.
  - cbn [zip_merge] in *.
    repeat rewrite atm_in_cons. rewrite Lclauses.in_merge_or.
    rewrite IH. tauto.
Qed.
Global Hint Rewrite in_zip_merge_or : ct.

Arguments zip_merge : simpl never.


(** * Helpers *)

Definition first_ctx (mc0 : t) :=
  match mc0 with
  | [] => Lclauses.empty
  | l0::_ => l0
  end.


Definition next_ctx (mc0 : t) :=
  match mc0 with
  | [] => []
  | _::mc1 => mc1
  end.


Lemma force_first_ctx : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (mc0 : t),
  force M w0 mc0 ->
  Lclauses.force M w0 (first_ctx mc0).
Proof.
  intros * Hforce.
  destruct mc0 as [|l0 mc1].
  - cbn. now apply Lclauses.force_empty.
  - apply Hforce.
Qed.

Definition with_first_cpls mc0 f :=
  let l0 := first_ctx mc0 in
  let mc1 := next_ctx mc0 in
  Lclauses.make (f (Lclauses.cpls l0)) (Lclauses.boxes l0) (Lclauses.dias l0) :: mc1.
Arguments with_first_cpls mc0 f /.

Definition add_cs mc0 cs :=
  with_first_cpls mc0 (cons (List.map Lit.Neg cs)).
Arguments add_cs mc0 cs /.

(** Adds the conjunction of each literal in [A]. *)
Definition add_A mc0 A :=
  with_first_cpls mc0 (app (Cnf.from_assumptions A)).
Arguments add_A mc0 A /.

(** Adds [~A] to the cpls of [mc0] via adding the disjunction of
    the negation of each literal in [A]. *)
Definition add_nA mc0 A :=
  with_first_cpls mc0 (cons (List.map Lit.negate A)).
Arguments add_nA mc0 A /.



(** * Extensions *)

(** Order that cpls are made matters for [add_cs_kt] to hold. *)
Fixpoint add_kt (mc0 : t) : t :=
  match mc0 with
  | [] => []
  | Lclauses.make cpls0 boxes0 dias0 :: mc1 =>
    (* a -> b for each a -> []b in the current context *)
    let unboxed := List.map (fun '(a, b) => [Lit.Neg a; b]) boxes0 in
    let mc1_kt := add_kt mc1 in
    (* Add all clauses from the next modal context *)
    Lclauses.merge
      (Lclauses.make (cpls0++unboxed) boxes0 dias0)
      (first_ctx mc1_kt)
    :: mc1_kt
  end.


Lemma add_cs_kt : forall mc0 cs,
  add_cs (Mcnf.add_kt mc0) cs =
  Mcnf.add_kt (add_cs mc0 cs).
Proof.
  intros *. destruct mc0 as [|[cpls boxes dias] mc1]; reflexivity.
Qed.


Lemma add_kt_tail : forall l0 mc1,
  next_ctx (add_kt (l0::mc1)) = add_kt mc1.
Proof.
  intros l0 mc1. destruct l0. cbn. reflexivity.
Qed. Global Hint Rewrite add_kt_tail : ct.


Lemma kt_force_unboxed : forall {W R} `{Reflexive W R} (M : @Kripke.t W R) (w0 : W) (boxes0 : list BoxClause.t),
  List.Forall (BoxClause.force M w0) boxes0 ->
  Cnf.force M w0 (List.map (fun '(a, b) => [Lit.Neg a; b]) boxes0).
Proof.
  intros * Hrefl * Hf_boxes.
  cbn. rewrite List.Forall_forall, Cnf.force_forall in *.
  intros cl Hcl_in.
  rewrite List.in_map_iff in Hcl_in.
  destruct Hcl_in as [[a b] [Hab Hab_in]].
  subst cl.
  rewrite CplClause.force_exists.

  specialize (Hf_boxes (a,b) Hab_in). cbn in *.
  destruct (classic (Kripke.valuation M w0 a)) as [Hf_a | Hnf_b].
  - specialize (Hf_boxes Hf_a w0). forward Hf_boxes by reflexivity.
    exists b. cbn. tauto.
  - exists (Lit.Neg a). tauto.
Qed.


Lemma add_kt_refl : forall {W} {R} `{Reflexive W R} (M : @Kripke.t W R) (w0 : W) (mc0 : t),
  Mcnf.force M w0 (add_kt mc0) <-> Mcnf.force M w0 mc0.
Proof with try easy; auto.
  intros * Hrefl *. revert w0. induction mc0 as [|l0 mc1 IH]; intros w0.
  { tauto. }

  destruct l0 as [cpls0 boxes0 dias0].
  split.
  (* add -> unadded easy as add_kt only adds extra clauses *)
  - cbn. rewrite Lclauses.force_merge_app_sym. autorewrite with ct.
    setoid_rewrite <- IH. tauto.

  - intros Hf. cbn. rewrite Lclauses.force_merge_app_sym. autorewrite with ct.
    split; [split|].
    (* force unboxed + originals *)
    + split.
      * apply kt_force_unboxed. apply Hf.
      * apply Hf.
    (* force fst ctx of mc1 *)
    + apply force_first_ctx. apply IH.
      (* w0 forces mc1 by reflexivity *)
      apply Hf. reflexivity.
    + setoid_rewrite IH. apply Hf.
Qed.

Corollary add_kt_sound : forall phi,
  satisfiable_kt phi -> satisfiable (add_kt phi).
Proof.
  intros phi Hsatkt_phi. unfold satisfiable, satisfiable_kt in *.
  deex. exists W,R,M,w0. now rewrite add_kt_refl.
Qed.



Lemma force_add_kt_next : forall {W R} (M : @Kripke.t W R) w0 mc0,
  force M w0 (add_kt mc0) ->
  force M w0 (add_kt (next_ctx mc0)).
Proof with try easy.
  intros *. revert w0. induction mc0 as [|l0 mc1 IH]...
  intros w0 Hfadd_mc0.
  destruct l0 as [cpls0 boxes0 dias0].
  destruct mc1 as [|l1 mc2]...
  destruct l1 as [cpls1 boxes1 dias1].

  cbn in *. autorewrite with ct in *.
  split.
  - apply Hfadd_mc0.
  - intros w1 HR_w1. apply IH. now apply Hfadd_mc0.
Qed.


Lemma force_refl_closure : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (mc0 : t),
  force M w0 (add_kt mc0) ->
  force (Kripke.make W (refl_closure R) (Kripke.valuation M)) w0 mc0.
Proof with try easy.
  intros *. revert w0.
  set (R' := refl_closure R).
  set (M' := Kripke.make W R' (Kripke.valuation M)).
  induction mc0 as [|l0 mc1 IH]...

  intros w0 Hfadd_mc0. destruct l0 as [cpls0 boxes0 dias0].
  cbn in Hfadd_mc0. autorewrite with ct in Hfadd_mc0.
  rewrite Lclauses.force_destruct in Hfadd_mc0.

  repeat rewrite and_assoc in Hfadd_mc0.
  destruct Hfadd_mc0 as [Hf_cpls0 [Hf_unboxed [Hf_boxes0 [Hf_dias0 [Hfadd_l1 Hfadd_mc1]]]]].

  cbn. repeat split.
  - apply (Cnf.force_local M' M)...

  - cbn.
    rewrite Cnf.force_map in Hf_unboxed.
    rewrite List.Forall_forall in Hf_boxes0 |- *.

    intros (a,b) Hab_in Hval_a w1 HR'_w1.
    specialize (Hf_unboxed (a,b) Hab_in).
    cbn in Hf_unboxed. rewrite CplClause.force_exists in Hf_unboxed.
    destruct Hf_unboxed as [l [[Hl_a | [Hl_b | F]] Hf_l]]...
    + subst l. cbn in Hf_l, Hval_a. contradiction.
    + subst l. apply Lit.force_local with (M1 := M)...
      destruct HR'_w1 as [HR_w1 | Hw0w1].
      * apply (Hf_boxes0 (a,b))...
      * now subst w1.

  - rewrite List.Forall_forall in Hf_dias0 |- *.
    intros (c,d) Hcd_in Hval_c.
    specialize (Hf_dias0 (c,d) Hcd_in Hval_c).
    deex. exists w1. unfold R', refl_closure. tauto.

  - intros w1 [HR_w1 | Hw0w1].
    + apply IH. now apply Hfadd_mc1.
    + subst w1. apply IH.
      apply force_add_kt_next with (mc0 := Lclauses.empty::mc1). cbn. split.
      * unfold Lclauses.merge. cbn. apply Hfadd_l1.
      * apply Hfadd_mc1.
Qed.

Corollary add_kt_complete : forall phi,
  satisfiable (add_kt phi) -> satisfiable_kt phi.
Proof.
  intros phi Hsatadd_phi.
  unfold satisfiable, satisfiable_kt in *.
  deex. exists W, (refl_closure R), _, (Kripke.make W (refl_closure R) (Kripke.valuation M)), w0.
  now apply force_refl_closure.
Qed.

Theorem add_kt_sound_complete : forall phi,
  satisfiable_kt phi <-> satisfiable (add_kt phi).
Proof.
  intros phi. split.
  - apply add_kt_sound.
  - apply add_kt_complete.
Qed.
