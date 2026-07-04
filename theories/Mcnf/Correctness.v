From CegarTableaux Require Lit Nnf Kripke Mclause.
From CegarTableaux.Mcnf Require Mcnf Conversion.
From CegarTableaux Require Import ImportStd Utils.

(** Shorter alias for conversion functions *)
Module Mcnfc := Conversion.


Lemma zip_merge_nil_l : forall B, Mcnfc.zip_merge [] B = B.
Proof. intros. cbn. destruct B; reflexivity. Qed.
Lemma zip_merge_nil_r : forall A, Mcnfc.zip_merge A [] = A.
Proof. intros. cbn. destruct A; reflexivity. Qed.

Lemma atm_in_cons : forall p l0 mc1, Mcnf.atm_in p (l0::mc1) <-> Lclauses.atm_in p l0 \/ Mcnf.atm_in p mc1.
Proof. intros. cbn. autorewrite with datatypes. reflexivity. Qed.

Lemma in_merge_or : forall (A B : Lclauses.t) (p : nat),
  Lclauses.atm_in p (Lclauses.merge A B) <-> Lclauses.atm_in p A \/ Lclauses.atm_in p B.
Proof.
  intros *.
  destruct A as [Acpls Aboxes Adias].
  destruct B as [Bcpls Bboxes Bdias].
  cbn. repeat rewrite Exists_app. tauto.
Qed.

Lemma in_zip_merge_or :
  forall (A B : Mcnf.t) (p : nat),
  Mcnf.atm_in p (Mcnfc.zip_merge A B) <-> Mcnf.atm_in p A \/ Mcnf.atm_in p B.
Proof.
  intros A B p. revert B.
  induction A as [| Al0 Amc1 IH]; intro B; destruct B as [|Bl0 Bmc1].
  - cbn. autorewrite with datatypes. tauto.
  - cbn. autorewrite with datatypes. tauto.
  - cbn. autorewrite with datatypes. tauto.
  - cbn [Mcnfc.zip_merge] in *.
    repeat rewrite atm_in_cons. rewrite in_merge_or.
    rewrite IH. tauto.
Qed.



  Lemma force_zip_and : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (A B : Mcnf.t),
    Mcnf.force M w0 (Mcnfc.zip_merge A B) <-> Mcnf.force M w0 A /\ Mcnf.force M w0 B.
  Proof.
    intros W R M w0 A. revert w0.

    (* induction on A, case-by-case on arbitrary B *)
    induction A as [|ha ta IHta]; intros w0 B; destruct B as [| hb tb].
    (* trivial empty cases *)
    - cbn. tauto.
    - cbn. tauto.
    - cbn. tauto.
    (* merge (ha::ta) (hb::tb) <-> (ha::ta) and (hb::tb) *)
    - cbn [Mcnfc.zip_merge Mcnf.force].
      rewrite Lclauses.force_merge_and.
      setoid_rewrite IHta.
      intuition (auto with solve_subterm).
  Qed.


Lemma sur_input_le_return :
  forall (n : nat) (phi : Nnf.t) (k : nat),
    k <= snd (Mcnfc.from_n_nnf n phi k).
Proof with auto.
  intros n phi k.
  revert n k.
  induction phi as
    [ l
    | A IHA B IHB
    | A IHA B IHB
    | A IHA
    | A IHA
    ]; cbn; intros n k.
  - reflexivity.
  - repeat destruct_pair. cbn.
    transitivity k0; subst k0 k1...
  - repeat destruct_pair. cbn.
    transitivity (S (S k))...
    transitivity k0; subst k0 k1...
  - destruct_pair. cbn.
    transitivity (S k); subst k0...
  - destruct_pair. cbn.
    transitivity (S k); subst k0...
Qed.


(** An extra tactic [autolia] that is equivalent to [lia] but applies some
    known inequalities from the above theorems. *)
Local Ltac add_ineq_from_sym_in_nnf :=
  match goal with
  | [ H: Nnf.atm_in ?x ?phi |- _ ] =>
      let T := constr:(x <= Nnf.max_atm phi) in
      (* assertion already known: fail *)
      tryif assert T by assumption then
        fail 1
      else
        let Hle := fresh "Hsym_le" in
        assert (T) as Hle by (apply Nnf.atm_le_max; exact H);
        clear H
  end.

Local Ltac add_ineq_from_n_impl :=
  match goal with
  | [ q := snd (Mcnfc.from_n_nnf ?name ?phi ?sur) |- _ ] =>
      let T := constr:(sur <= q) in
      tryif assert T by assumption then
        fail 1
      else
        let Hle := fresh "Hsur_le" in
        assert (T) as Hle by (unfold q; apply sur_input_le_return);
        (* since we clear it, lia can't solve if we have an unfolded version of q *)
        fold_all q;
        clearbody q
  end.

Local Ltac add_ineqs := repeat ((add_ineq_from_sym_in_nnf; []) || (add_ineq_from_n_impl; [])).

Local Ltac autolia :=
  add_ineqs;
  lia.

(** Solve the current goal with a variety of autosolvers which are likely
    to solve goals relating to the current context.

    This fails if the goal cannot be completely solved. *)
Local Ltac finish := solve [ cbn; (try ifauto); auto; (try autolia); (try tauto); (try easy)].


Theorem conv_atm_range :
  forall
    (phi : Nnf.t)
    (n k : nat)
    (Hmnp_lt : Nnf.max_atm phi < n < k)
    (p : nat),
  Mcnf.atm_in p (fst (Mcnfc.from_n_nnf n phi k)) ->
  Nnf.atm_in p phi
    \/ p = n
    \/ k <= p < (snd (Mcnfc.from_n_nnf n phi k)).
Proof with finish.
  intros phi n k Hmnp_lt p.
  revert n k Hmnp_lt.

  induction phi as
    [ l
    | A IHA B IHB
    | A IHA B IHB
    | A IHA
    | A IHA
    ]; intros n k Hmnp_lt.
  (* literal: p in phi or p = n *)
  - intro Hp_mcnf.
    repeat (autorewrite with datatypes in Hp_mcnf; cbn in Hp_mcnf).
    repeat rewrite or_false_l in Hp_mcnf.
    destruct Hp_mcnf as [Hnp | Hlp].
    (* n = p *)
    + rewrite Hnp...
    (* l = p *)
    + destruct l...

  (* and *)
  - cbn -[Mcnf.atm_in].
    destruct_pair (Mcnfc.from_n_nnf n A k) as [A_mcnf kA].
    destruct_pair (Mcnfc.from_n_nnf n B kA) as [B_mcnf kB].
    intro Hp_mcnf. cbn [fst] in Hp_mcnf.

    specialize (IHA n k).
    specialize (IHB n kA).

    cbn in Hmnp_lt.

    forward IHA by lia.
    forward IHB by autolia.

    fold A_mcnf kA in IHA.
    fold B_mcnf kB in IHB.

    rewrite in_zip_merge_or in Hp_mcnf.

    destruct Hp_mcnf as [Hp_A | Hp_B].
    + forward IHA by assumption.
      destruct IHA...
    + forward IHB by assumption.
      destruct IHB...

  (* or *)
  - cbn -[Mcnfc.zip_merge Mcnf.atm_in].
    destruct_pair (Mcnfc.from_n_nnf k A (S (S k))) as [A_mcnf kA].
    destruct_pair (Mcnfc.from_n_nnf (S k) B kA) as [B_mcnf kB].
    intro Hp_mcnf. cbn [fst] in Hp_mcnf.

    specialize (IHA k (S (S k))).
    specialize (IHB (S k) kA).

    cbn in Hmnp_lt.
    forward IHA by lia.
    forward IHB by autolia.

    fold A_mcnf kA in IHA.
    fold B_mcnf kB in IHB.

    repeat rewrite in_zip_merge_or in Hp_mcnf.

    destruct Hp_mcnf as [Hp_cpls | [Hp_A | Hp_B]].
    + repeat (autorewrite with datatypes in Hp_cpls; cbn in Hp_cpls).
      repeat rewrite or_false_l in Hp_cpls. cbn [snd].
      autolia.
    + forward IHA by assumption.
      destruct IHA...
    + forward IHB by assumption.
      destruct IHB...

  (* box *)
  - cbn -[Mcnfc.zip_merge Mcnf.atm_in].
    destruct_pair (Mcnfc.from_n_nnf k A (S k)) as [A_mcnf kA].
    intro Hp_mcnf. cbn [fst] in Hp_mcnf.

    cbn in Hmnp_lt.
    specialize (IHA k (S k)).
    forward IHA by lia.

    fold A_mcnf kA in IHA.

    rewrite atm_in_cons in Hp_mcnf. destruct Hp_mcnf as [Hp_box | Hp_A].
    + cbn in Hp_box. autorewrite with datatypes fold_prop in Hp_box.
      cbn in Hp_box. cbn. autolia.
    + forward IHA by assumption.
      destruct IHA...

  (* dia: identical to box case *)
  - cbn -[Mcnfc.zip_merge Mcnf.atm_in].
    destruct_pair (Mcnfc.from_n_nnf k A (S k)) as [A_mcnf kA].
    intro Hp_mcnf. cbn [fst] in Hp_mcnf.

    cbn in Hmnp_lt.
    specialize (IHA k (S k)).
    forward IHA by lia.

    fold A_mcnf kA in IHA.

    rewrite atm_in_cons in Hp_mcnf. destruct Hp_mcnf as [Hp_box | Hp_A].
    + cbn in Hp_box. autorewrite with datatypes fold_prop in Hp_box.
      cbn in Hp_box. cbn. autolia.
    + forward IHA by assumption.
      destruct IHA...
Qed.


(** Construction of a model that forces the converted formula. *)
Section EquisatModel.
  Definition set_kripke_at_n_iff_force
    {W} {R}
    (** the model to change at n *)
    (Mmcnf : @Kripke.t W R) (n : nat)
    (** at n, set valuation to Nnf.force Mnnf w phi *)
    (Mnnf : @Kripke.t W R) (phi : Nnf.t)
    : @Kripke.t W R :=
    Kripke.make W R (fun w x => if x =? n then Nnf.force Mnnf w phi else Kripke.valuation Mmcnf w x).


  (** Transforms [M] so that [M] forces [n -> phi] iff [M'] forces [n -> phi']
      Requires that [Nnf.max_atm phi < n < k]. *)
  Fixpoint named_model {W} {R} (M : @Kripke.t W R) (n : nat) (phi : Nnf.t) (k : nat) : @Kripke.t W R :=
    match phi with
    (* n -> l  =>  ~n \/ l *)
    | Nnf.Lit l =>
        set_kripke_at_n_iff_force M n M phi

    (* n -> A /\ B  =>  n -> A ; n -> B *)
    | Nnf.And A B =>
      let M' := named_model M n A k in
      let k := snd (Mcnfc.from_n_nnf n A k) in
      let M' := named_model M' n B k in
        set_kripke_at_n_iff_force M' n M phi

    (* n -> A \/ B  =>  n -> nA \/ nB ; nA -> A ; nB -> B *)
    | Nnf.Or A B =>
      let (nA, k) := (k, S k) in
      let (nB, k) := (k, S k) in
      let M' := named_model M nA A k in
      let k := snd (Mcnfc.from_n_nnf nA A k) in
      let M' := named_model M' nB B k in
        set_kripke_at_n_iff_force M' n M phi

    (* n -> []A  =>  n -> []nA ; [](nA -> A) *)
    | Nnf.Box A =>
      let (nA, k) := (k, S k) in
      let M' := named_model M nA A k in
        set_kripke_at_n_iff_force M' n M phi

    (* n -> <>A  =>  n -> <>nA ; [](nA -> A) *)
    | Nnf.Dia A =>
      let (nA, k) := (k, S k) in
      let M' := named_model M nA A k in
        set_kripke_at_n_iff_force M' n M phi
    end.
End EquisatModel.



(** Lemmas about the atoms that the named model changes. *)
Section EquisatModelRange.
  Lemma named_model_changes_sur_only :
    forall {W} {R} (M : @Kripke.t W R) (w : W) (phi : Nnf.t) (n k p : nat) (Hmnp_lt : Nnf.max_atm phi < n < k),
      let k' := snd (Mcnfc.from_n_nnf n phi k) in
      ~ (p = n \/ k <= p < k') ->
      Kripke.valuation M w p <-> Kripke.valuation (named_model M n phi k) w p.
  Proof with simpl; auto; try autolia.
    intros W R M w phi.
    revert M w.
    induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ];
      intros M w n k p Hmnp_lt k' Hx_range; apply not_or_and in Hx_range.
    (* literal *)
    - simpl. ifauto. reflexivity.

    (* and *)
    - set (MA := named_model M n A k).
      set (kA := snd (Mcnfc.from_n_nnf n A k)).
      set (MB := named_model MA n B kA).
      set (kB := snd (Mcnfc.from_n_nnf n B kA)).
      simpl in Hmnp_lt.
      assert (kA <= k') as Hqs.
      {
        unfold k'. simpl.
        repeat inline_pair. simpl.
        fold kA. apply sur_input_le_return.
      }
      assert (kB = k') as Hrs.
      {
        unfold k'. simpl.
        repeat inline_pair. simpl.
        fold kA. fold kB. reflexivity.
      }

      assert (Kripke.valuation M w p <-> Kripke.valuation MA w p) as Hval_M_MA.
      {
        unfold MA. apply IHA...
        fold kA. autolia.
      }
      assert (Kripke.valuation MA w p <-> Kripke.valuation MB w p) as Hval_MA_MB.
      {
        unfold MB. apply IHB...
        fold kB. autolia.
      }

      simpl. ifauto. fold MA kA MB. tauto.

    (* or *)
    - set (MA := named_model M k A (S (S k))).
      set (kA := snd (Mcnfc.from_n_nnf k A (S (S k)))).
      set (MB := named_model MA (S k) B kA).
      set (kB := snd (Mcnfc.from_n_nnf (S k) B kA)).

      simpl in Hmnp_lt.
      assert (kA <= k') as Hqs.
      {
        unfold k'. simpl.
        repeat inline_pair. simpl.
        fold kA. apply sur_input_le_return.
      }
      assert (kB = k') as Hrs.
      {
        unfold k'. simpl.
        repeat inline_pair. simpl.
        fold kA. fold kB. reflexivity.
      }

      assert (Kripke.valuation M w p <-> Kripke.valuation MA w p) as Hval_M_MA.
      {
        unfold MA. apply IHA...
        fold kA. autolia.
      }
      assert (Kripke.valuation MA w p <-> Kripke.valuation MB w p) as Hval_MA_MB.
      {
        unfold MB. apply IHB...
        fold kB. autolia.
      }

      simpl. ifauto. fold MA kA MB. tauto.

    (* box *)
    - simpl. simpl in Hmnp_lt. ifauto.

      set (kA := snd (Mcnfc.from_n_nnf k A (S k))).
      assert (kA = k').
      { unfold k'. simpl. inline_pair. simpl. reflexivity. }

      apply IHA... fold kA. autolia.

    (* dia *)
    - simpl. simpl in Hmnp_lt. ifauto.

      set (kA := snd (Mcnfc.from_n_nnf k A (S k))).
      assert (kA = k').
      { unfold k'. simpl. inline_pair. simpl. reflexivity. }

      apply IHA... fold kA. autolia.
  Qed.


  Lemma named_model_vals_name_iff_force :
    forall {W} {R} (M : @Kripke.t W R) (w : W) (phi : Nnf.t) (n k : nat),
      Kripke.valuation (named_model M n phi k) w n <-> Nnf.force M w phi.
  Proof.
    intros W R M w phi. revert w.
      induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ];
    intros w n k; simpl; ifauto; reflexivity.
  Qed.


  Lemma named_model_overrides_all_sur :
    forall {W} {R} (M M' : @Kripke.t W R) (w : W) (phi : Nnf.t) (n k p : nat) (Hmnp_lt : Nnf.max_atm phi < n < k),
      let k' := snd (Mcnfc.from_n_nnf n phi k) in
      k <= p < k' ->
      Nnf.agree phi M M' ->
      Kripke.valuation (named_model M n phi k) w p <->
      Kripke.valuation (named_model M' n phi k) w p.
  Proof with simpl; auto; try autolia.
    intros W R M M' w phi.
    revert M M' w.

    induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ];
    intros M M' w n k p Hmnp_lt k' Hx_range Hmodels_agree.
    (* holds because k' = k, the range is empty *)
    - simpl in k'. simpl. ifauto. lia.

    - set (MA := named_model M n A k).
      set (kA := snd (Mcnfc.from_n_nnf n A k)).
      set (MB := named_model MA n B kA).
      set (kB := snd (Mcnfc.from_n_nnf n B kA)).

      set (M'A := named_model M' n A k).
      set (M'B := named_model M'A n B kA).

      simpl in Hmnp_lt.
      assert (kA <= k') as Hqs.
      {
        unfold k'. simpl.
        repeat inline_pair. simpl.
        fold kA. apply sur_input_le_return.
      }
      assert (kB = k') as Hrs.
      {
        unfold k'. simpl.
        repeat inline_pair. simpl.
        fold kA. fold kB. reflexivity.
      }
      cbn. ifauto. fold MA M'A kA MB M'B.

      assert (k <= p < kA \/ kA <= p < k') as [Hpxq | Hqxs] by lia.
      (* k <= p < kA *)
      + assert (Kripke.valuation MA w p <-> Kripke.valuation MB w p) as Hval_MA_MB.
        { unfold MB. apply named_model_changes_sur_only... }
        assert (Kripke.valuation M'A w p <-> Kripke.valuation M'B w p) as Hval_M'A_M'B.
        { unfold MB. apply named_model_changes_sur_only... }
        rewrite <- Hval_MA_MB.
        rewrite <- Hval_M'A_M'B.
        apply IHA...
        apply (Nnf.agree_l A B). assumption.

      (* q <= p < s *)
      + unfold MB, M'B.
        apply IHB...
        * fold kB. lia.
        * intros w' p' Hx'_in_B.
          unfold MA, M'A.
          rewrite <- (named_model_changes_sur_only M')...
          rewrite <- (named_model_changes_sur_only M)...
          apply (Nnf.agree_r A B)...

    - set (MA := named_model M k A (S (S k))).
      set (q := snd (Mcnfc.from_n_nnf k A (S (S k)))).
      set (MB := named_model MA (S k) B q).
      set (r := snd (Mcnfc.from_n_nnf (S k) B q)).

      set (M'A := named_model M' k A (S (S k))).
      set (M'B := named_model M'A (S k) B q).


      simpl in Hmnp_lt.
      assert (q <= k') as Hqs.
      {
        unfold k'. simpl.
        repeat inline_pair. simpl.
        fold q. apply sur_input_le_return.
      }
      assert (r = k') as Hrs.
      {
        unfold k'. simpl.
        repeat inline_pair. simpl.
        fold q. fold r. reflexivity.
      }

      simpl. ifauto. fold MA M'A q MB M'B.
      assert (p = k \/ p = S k \/ (S (S k)) <= p < q \/ q <= p < k') as [Hxp | [HxSp | [Hpxq | Hqxs]]] by lia.
      (* p = k *)
      + unfold MB, M'B.
        rewrite <- (named_model_changes_sur_only M'A)...
        rewrite <- (named_model_changes_sur_only MA)...
        unfold MA, M'A.
        rewrite Hxp.
        repeat rewrite named_model_vals_name_iff_force.
        apply Nnf.meaningful_valuations.
        apply (Nnf.agree_l A B). assumption.

      (* p = S k *)
      + unfold MB, M'B.
        rewrite HxSp.
        repeat rewrite named_model_vals_name_iff_force.
        apply Nnf.meaningful_valuations.
        unfold Nnf.agree.
        (* MA and M'A agree *)
        intros w' p' Hx'_in_B.
        unfold MA, M'A.
        rewrite <- (named_model_changes_sur_only M')...
        rewrite <- (named_model_changes_sur_only M)...
        apply (Nnf.agree_r A B)...

      (* S (S k) <= p < q *)
      + assert (Kripke.valuation MA w p <-> Kripke.valuation MB w p) as Hval_MA_MB.
        { unfold MB. apply named_model_changes_sur_only... }
        assert (Kripke.valuation M'A w p <-> Kripke.valuation M'B w p) as Hval_M'A_M'B.
        { unfold MB. apply named_model_changes_sur_only... }
        rewrite <- Hval_MA_MB.
        rewrite <- Hval_M'A_M'B.
        apply IHA...
        apply (Nnf.agree_l A B)...

      (* q <= p < k' *)
      + unfold MB, M'B.
        apply IHB...
        * fold r. lia.
        * intros w' p' Hx'_in_B.
          unfold MA, M'A.
          rewrite <- (named_model_changes_sur_only M')...
          rewrite <- (named_model_changes_sur_only M)...
          apply (Nnf.agree_r A B)...

    - simpl. simpl in Hmnp_lt. ifauto.
      set (q := snd (Mcnfc.from_n_nnf k A (S k))).
      assert (q = k') as Hqs.
      { unfold k'. simpl. inline_pair. simpl. reflexivity. }

      assert (p = k \/ S k <= p < k') as [Hxp | HSpxs] by lia.
      + rewrite Hxp.
        repeat rewrite named_model_vals_name_iff_force.
        apply Nnf.meaningful_valuations. assumption.
      + apply IHA... fold q. lia.

    - simpl. simpl in Hmnp_lt. ifauto.
      set (q := snd (Mcnfc.from_n_nnf k A (S k))).
      assert (q = k') as Hqs.
      { unfold k'. simpl. inline_pair. simpl. reflexivity. }

      assert (p = k \/ S k <= p < k') as [Hxp | HSpxs] by lia.
      + rewrite Hxp.
        repeat rewrite named_model_vals_name_iff_force.
        apply Nnf.meaningful_valuations. assumption.
      + apply IHA... fold q. lia.
  Qed.
End EquisatModelRange.












(** Inductive proof of NNF to MCNF satisfiability. *)
Section NnfToMcnf.
  Context {W : Type}.
  Context {R : relation W}.
  Context {M : @Kripke.t W R}.

  Definition with_global_val {W} {R} (M : @Kripke.t W R) (p : nat) (val : W -> Prop) :=
    Kripke.make W R (fun w p' => if p =? p' then val w else Kripke.valuation M w p').

  Definition IH phi :=
    forall w0 n p, Nnf.max_atm phi < n < p ->
    let M' := named_model M n phi p in
    (* unset n to be arbitrary, still forces *)
    forall (n_val : W -> Prop),
    (forall w, n_val w -> Nnf.force M w phi) ->
    Mcnf.force (with_global_val M' n n_val) w0 (fst (Mcnfc.from_n_nnf n phi p)).


  Lemma lit_sat : forall (l : Lit.t), IH (Nnf.Lit l).
  Proof with try finish.
    intros l w0 n k Hmnk_lt.
    cbn. split... autorewrite with datatypes fold_prop.
    cbn.
    pose proof (classic (Nnf.force M w0 (Nnf.Lit l))) as [HM_force_l | HM_nforce_l].
    (* forces l *)
    + exists l. cbn in *. split...
      destruct l as [x|x]; cbn in *; ifauto.
    (* does not force l *)
    + exists (Lit.Neg n). cbn in *. split...
  Qed.


  Lemma and_sat : forall (A B : Nnf.t) (IHA : IH A) (IHB : IH B), IH (Nnf.And A B).
  Proof with try finish.
    intros A B IHA IHB w0 n k Hmnk_lt M' n_val Hn_val.
    cbn.
    destruct_pair as [A_mcnf kA].
    destruct_pair as [B_mcnf kB].
    cbn in *.

    set (MA := named_model M n A k).
    set (MB := named_model MA n B kA).
    (* assert (S (S p) <= q) as Hpq. { unfold q. apply sur_input_le_return. }
    assert (q <= r) as Hqr. { unfold r. apply sur_input_le_return. } *)

    fold MA kA MB in M'. fold M'.

    specialize (IHA w0 n k). forward IHA by lia.
    fold MA A_mcnf in IHA. cbn in IHA.
    specialize (IHB w0 n kA). forward IHB by autolia.
    set (MBIH := named_model M n B kA) in IHB.
    fold B_mcnf in IHB. cbn in IHB.

    rewrite force_zip_and.

    split.

    (* M' |= A_mcnf *)
    - specialize (IHA n_val). 
      forward IHA. { intros w. specialize (Hn_val w). tauto. }
      eapply (Mcnf.meaningful_valuations). 2: { exact IHA. }

      intros w p Hp_in.
      destruct (eq_dec n p) as [Hnp | Hn_ne_p]...
      cbn. ifauto.
      (* MB to MA *)
      subst MB. rewrite <- named_model_changes_sur_only...
      subst A_mcnf.
      apply conv_atm_range in Hp_in... destruct Hp_in...

    (* M' |= B_mcnf *)
    - specialize (IHB n_val).
      forward IHB. { intros w. specialize (Hn_val w). tauto. }
      eapply Mcnf.meaningful_valuations. 2: { exact IHB. }

      intros w p Hp_in.
      destruct (eq_dec n p) as [Hnp | Hn_ne_p]...
      cbn. ifauto.
      apply conv_atm_range in Hp_in...
      destruct Hp_in.
      + assert (Kripke.valuation M w p <-> Kripke.valuation MA w p) as Heqval_M_MA.
        { unfold MA. apply named_model_changes_sur_only... }
        assert (Kripke.valuation MA w p <-> Kripke.valuation MB w p) as Heqval_MA_MB.
        { unfold MB. apply named_model_changes_sur_only...  }
        unfold MBIH. rewrite <- Heqval_MA_MB. rewrite <- Heqval_M_MA.
        apply named_model_changes_sur_only...
      + destruct H...
        unfold MB, MBIH.
        apply named_model_overrides_all_sur...
        intros w' x' Hx'_in_B.
        unfold MA. symmetry. apply named_model_changes_sur_only...
  Qed.


  Lemma or_sat : forall (A B : Nnf.t) (IHA : IH A) (IHB : IH B), IH (Nnf.Or A B).
  Proof with try finish.
    intros A B IHA IHB w0 n k Hmnk_lt M' n_val Hn_val.
    cbn -[Mcnfc.zip_merge].
    destruct_pair as [A_mcnf kA].
    destruct_pair as [B_mcnf kB].
    cbn -[Mcnfc.zip_merge] in *.

    set (MA := named_model M k A (S (S k))).
    set (MB := named_model MA (S k) B kA).
    fold MA kA MB in M'. fold M'.

    specialize (IHA w0 k (S (S k))). forward IHA by lia.
    fold MA A_mcnf in IHA. cbn in IHA.
    specialize (IHB w0 (S k) kA). forward IHB by autolia.
    set (MBIH := named_model M (S k) B kA).
    fold MBIH B_mcnf in IHB. cbn in IHB.

    repeat rewrite force_zip_and.
    split; [|split].
    (* forces ~n or k or S k *)
    - cbn. autorewrite with datatypes fold_prop.
      destruct (classic (Nnf.force M w0 (Nnf.Or A B))) as [[HM_force_A | HM_force_B] | HM_nforce_AB].
      (* M |= A *)
      + unfold M', set_kripke_at_n_iff_force.
        exists (Lit.Pos k). split... cbn. ifauto.
        unfold MB. rewrite <- named_model_changes_sur_only...
        unfold MA. apply named_model_vals_name_iff_force...
      (* M |= B *)
      + unfold M', set_kripke_at_n_iff_force.
        exists (Lit.Pos (S k)).
        (* simpl goes too far with S k, makes it hard to resolve. *)
        (* remember to avoid simplifying too far. *)
        remember (S k) as nB. split... cbn. ifauto.

        (* forces B <-> nB valued *)
        unfold MB. apply named_model_vals_name_iff_force...

        (* but MB is applied on top of. show that M and MA agree on A *)
        apply (Nnf.meaningful_valuations M MA)...
        unfold Nnf.agree.
        intros w x Hx_in_B.
        apply named_model_changes_sur_only...

      (* M |/= A /\ B *)
      (* then M' values ~n *)
      + unfold M', set_kripke_at_n_iff_force.
        exists (Lit.Neg n). split... cbn. ifauto.
        intro Hn_val_t. apply Hn_val in Hn_val_t. contradiction.

    (* forces A_mcnf *)
    - specialize (IHA (fun w => Nnf.force M w A)). forward IHA by tauto.
      eapply Mcnf.meaningful_valuations. 2: { exact IHA. }
      intros w p Hp_in.
      apply conv_atm_range in Hp_in...
      destruct Hp_in as [Hp_A | Hp_sur].
      + assert (p < n) as Hp_lt_n... cbn. ifauto.
        unfold MB.
        rewrite <- named_model_changes_sur_only...
      + cbn. ifauto.
        destruct Hp_sur.
        * subst p. ifauto. unfold MB.
          rewrite <- named_model_changes_sur_only...
          unfold MA. rewrite named_model_vals_name_iff_force...
        * ifauto. unfold MB.
          rewrite <- named_model_changes_sur_only...

    (* forces B_mcnf *)
    - specialize (IHB (fun w => Nnf.force M w B)). forward IHB by tauto.
      (* same as the model from IHB *)
      eapply Mcnf.meaningful_valuations. 2: { exact IHB. }

      intros w p Hp_in.
      apply conv_atm_range in Hp_in... fold kB in Hp_in.
      remember (S k) as sk. (* ifauto tries to simplify without this and can't do as much *)

      destruct Hp_in as [Hp_A | [Hp_sk | HkA_p_kB]].

      (* p in B *)
      + assert (p < n) as Hp_lt_n...
        cbn. ifauto.
        unfold MB, MBIH, MA.
        rewrite <- named_model_changes_sur_only...
        rewrite <- named_model_changes_sur_only...
        rewrite <- named_model_changes_sur_only...

      (* p = sk = name of B *)
      + cbn. ifauto.
        unfold MB. subst p sk.
        rewrite named_model_vals_name_iff_force...
        (* MA forces iff M forces *)
        rewrite (Nnf.meaningful_valuations M MA)...
        clear w. intros w p Hp_B.
        unfold MA. apply named_model_changes_sur_only...

      (* kA <= p < kB *)
      + cbn.
        assert (sk < kA) as Hsk_kA... ifauto. clear Hsk_kA.
        (* MB and MBIH agree *)
        unfold MB, MBIH.
        rewrite <- named_model_overrides_all_sur...

        (* M and MA agree on B *)
        intros w' p' Hp'_B.
        unfold MA. apply named_model_changes_sur_only...
  Qed.


  Lemma box_sat : forall (A : Nnf.t) (IHA : IH A), IH (Nnf.Box A).
  Proof with try finish.
    intros A IHA w0 n k Hmnk_lt M' n_val Hn_val.
    cbn.
    destruct_pair as [A_mcnf kA].

    cbn in *. autorewrite with datatypes fold_prop.
    split.
    (* forces box clause *)
    - cbn. ifauto. intros Hnval_w0 w1 HR_w1. ifauto.
      rewrite named_model_vals_name_iff_force.
      apply (Hn_val w0)...

    (* forces every adjacent *)
    - intros w1 HR_w1.
      unfold IH in IHA.
      specialize (IHA w1 k (S k)).
      forward IHA by lia.
      specialize (IHA (fun w => Nnf.force M w A)).
      forward IHA by tauto.
      fold A_mcnf in IHA.

      eapply Mcnf.meaningful_valuations. 2: { exact IHA. }
      intros w p Hp_in.
      apply conv_atm_range in Hp_in... fold kA in Hp_in.
      destruct Hp_in as [Hp_A | [Hpk | Hsk_p_kA]].
      + assert (p < n)...
      + cbn. ifauto. subst p. rewrite named_model_vals_name_iff_force...
      + cbn. ifauto...
  Qed.


  Lemma dia_sat : forall (A : Nnf.t) (IHA : IH A), IH (Nnf.Dia A).
  Proof with try finish.
    intros A IHA w0 n k Hmnk_lt M' n_val Hn_val.
    cbn.
    destruct_pair as [A_mcnf kA].

    cbn in *. autorewrite with datatypes fold_prop.
    split.
    (* forces dia clause *)
    - cbn. ifauto. intro Hn_val_w0.
      specialize (Hn_val w0 Hn_val_w0).
      destruct Hn_val as [w1 [HR_w1 Hw1_force_A]].
      exists w1. split...
      ifauto.
      rewrite named_model_vals_name_iff_force...

    (* forces every adjacent *)
    - intros w1 HR_w1.
      unfold IH in IHA.
      specialize (IHA w1 k (S k)).
      forward IHA by lia.
      specialize (IHA (fun w => Nnf.force M w A)).
      forward IHA by tauto.
      fold A_mcnf in IHA.

      eapply Mcnf.meaningful_valuations. 2: { exact IHA. }
      intros w p Hp_in.
      apply conv_atm_range in Hp_in... fold kA in Hp_in.
      destruct Hp_in as [Hp_A | [Hpk | Hsk_p_kA]].
      + assert (p < n)...
      + cbn. ifauto. subst p. rewrite named_model_vals_name_iff_force...
      + cbn. ifauto...
  Qed.


  Theorem M'_force_n_impl_phi :
    forall (phi : Nnf.t), IH phi.
  Proof with try easy.
    intros phi.

    induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ]; intros w0 n p Hmnp_lt M'.

    - apply lit_sat...
    - apply and_sat...
    - apply or_sat...
    - apply box_sat...
    - apply dia_sat...
  Qed.


  Theorem nnf_to_mcnf_forces :
    forall (w0 : W) (phi : Nnf.t) (n p : nat),
    Nnf.max_atm phi < n < p ->
    Nnf.force M w0 phi ->
    Mcnf.force
      (named_model M n phi p)
      w0
      (Mcnfc.from_nnf_with_sur n phi p).
  Proof with try finish.
    intros w0 phi n k Hmnk_lt HMforce_phi.
    unfold Mcnfc.from_nnf_with_sur.
    rewrite force_zip_and.
    split.
    (* force n *)
    - cbn. autorewrite with datatypes fold_prop.
      exists (Lit.Pos n). split...
      apply named_model_vals_name_iff_force...
    (* force the rest *)
    - pose proof (M'_force_n_impl_phi phi w0 n k Hmnk_lt) as IH.
      specialize (IH (fun w => Nnf.force M w phi)).
      forward IH by tauto.

      eapply Mcnf.meaningful_valuations. 2: { exact IH. }
      intros w p Hp_in.
      apply conv_atm_range in Hp_in...
      destruct Hp_in as [Hp_phi | [Hpn | Hk_p_k']].
      + assert (p < n)...
      + cbn. ifauto. subst p. rewrite named_model_vals_name_iff_force...
      + cbn. ifauto...
  Qed.
End NnfToMcnf.


Corollary sat_nnf_to_mcnf :
  forall (phi : Nnf.t), Nnf.satisfiable phi -> Mcnf.satisfiable (Mcnfc.from_nnf phi).
Proof with simpl; try lia; auto.
  intros phi Hphi_sat.
  unfold Nnf.satisfiable in Hphi_sat.
  destruct Hphi_sat as [W [R [M [w0 HM_force_phi]]]].

  unfold Mcnf.satisfiable.
  set (n := S (Nnf.max_atm phi)).
  exists W, R, (named_model M n phi (S n)), w0.
  apply nnf_to_mcnf_forces...
Qed.


(** Proof of backward implication. *)

Theorem mcnf_to_nnf_forces :
  forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : Nnf.t) (n k : nat) (Hmnk_lt : Nnf.max_atm phi < n < k),
  Mcnf.force M w0 (Mcnfc.from_nnf_with_sur n phi k) -> Nnf.force M w0 phi.
Proof with try finish.
  intros W R M w0 phi.
  revert w0.

  induction phi as
    [ l
    | A IHA B IHB
    | A IHA B IHB
    | phi IHphi
    | phi IHphi
    ]; intros w0 n k Hmnk_lt Hforce_mcnf.

  - cbn in Hforce_mcnf |- *. autorewrite with datatypes fold_prop in Hforce_mcnf.
    destruct Hforce_mcnf as [HM_val_n HM_force_nn_l].

    destruct HM_val_n as [p [[Hpn | F] Hforce_n]]... subst p.
    cbn in Hforce_n.

    cbn in HM_force_nn_l.
    destruct HM_force_nn_l as [l' [[Hl'_nn | [Hll' | F]] Hforce_l']]...
    + subst l'. contradiction.
    + subst l'. assumption.

  (* and *)
  - cbn in Hmnk_lt.
    unfold Mcnfc.from_nnf_with_sur in Hforce_mcnf.
    cbn [Mcnfc.from_n_nnf] in Hforce_mcnf.
    destruct_pair in Hforce_mcnf as [A_mcnf kA].
    destruct_pair in Hforce_mcnf as [B_mcnf kB].
    cbn [fst] in Hforce_mcnf.

    repeat rewrite force_zip_and in Hforce_mcnf.
    destruct Hforce_mcnf as [Hforce_n [Hforce_A Hforce_B]].

    split.
    (* forces A *)
    + apply (IHA w0 n k)...
      unfold Mcnfc.from_nnf_with_sur.
      apply force_zip_and...
    (* forces B *)
    + apply (IHB w0 n kA)...
      unfold Mcnfc.from_nnf_with_sur.
      apply force_zip_and...

  (* or *)
  - cbn in Hmnk_lt.
    unfold Mcnfc.from_nnf_with_sur in Hforce_mcnf.
    cbn [Mcnfc.from_n_nnf] in Hforce_mcnf.
    destruct_pair in Hforce_mcnf as [A_mcnf kA].
    destruct_pair in Hforce_mcnf as [B_mcnf kB].
    cbn [fst] in Hforce_mcnf.

    repeat rewrite force_zip_and in Hforce_mcnf.
    cbn in Hforce_mcnf. autorewrite with datatypes fold_prop in *.
    destruct Hforce_mcnf as [Hforce_n [Hforce_n_k_Sk [Hforce_A Hforce_B]]].

    destruct Hforce_n as [l [[Hnl | F] Hforce_n]]... subst l.
    destruct Hforce_n_k_Sk as [l [Hl_in Hforce_l]].
    destruct Hl_in as [Hl_nn | [Hl_k | [Hl_Sk | F]]]...
    (* must force n, contradiction *)
    + subst l...
    + subst l. left.
      apply (IHA w0 k (S (S k)))...
      unfold Mcnfc.from_nnf_with_sur. fold A_mcnf.
      rewrite force_zip_and.
      split...
      cbn. autorewrite with datatypes fold_prop in *.
      exists (Lit.Pos k)...
    + subst l. right.
      apply (IHB w0 (S k) kA)...
      unfold Mcnfc.from_nnf_with_sur. fold B_mcnf.
      rewrite force_zip_and.
      split...
      cbn. autorewrite with datatypes fold_prop in *.
      exists (Lit.Pos (S k))...

  (* box *)
  - cbn in Hmnk_lt.
    unfold Mcnfc.from_nnf_with_sur in Hforce_mcnf.
    cbn [Mcnfc.from_n_nnf] in Hforce_mcnf.
    destruct_pair in Hforce_mcnf as [A_mcnf kA].
    cbn [fst] in Hforce_mcnf.

    rewrite force_zip_and in Hforce_mcnf.
    cbn in Hforce_mcnf. autorewrite with datatypes fold_prop in *.
    destruct Hforce_mcnf as [Hforce_n [Hforce_n_k Hforce_w1]].

    destruct Hforce_n as [l [[Hnl | F] Hforce_n]]... subst l.
    cbn in Hforce_n_k. forward Hforce_n_k by assumption.

    cbn. intros w1 HR_w1.
    apply (IHphi w1 k (S k))...
    unfold Mcnfc.from_nnf_with_sur. rewrite force_zip_and.
    split...
    cbn. autorewrite with datatypes fold_prop. cbn.
    exists (Lit.Pos k)...

  (* dia *)
  - cbn in Hmnk_lt.
    unfold Mcnfc.from_nnf_with_sur in Hforce_mcnf.
    cbn [Mcnfc.from_n_nnf] in Hforce_mcnf.
    destruct_pair in Hforce_mcnf as [A_mcnf kA].
    cbn [fst] in Hforce_mcnf.

    rewrite force_zip_and in Hforce_mcnf.
    cbn in Hforce_mcnf. autorewrite with datatypes fold_prop in *.
    destruct Hforce_mcnf as [Hforce_n [Hforce_n_k Hforce_w1]].

    destruct Hforce_n as [l [[Hnl | F] Hforce_n]]... subst l.
    cbn in Hforce_n_k. forward Hforce_n_k by assumption.
    destruct Hforce_n_k as [w1 [HR_w1 Hforce_k]].

    cbn. exists w1. split...
    apply (IHphi w1 k (S k))...
    unfold Mcnfc.from_nnf_with_sur. rewrite force_zip_and.
    split...
    cbn. autorewrite with datatypes fold_prop. cbn.
    exists (Lit.Pos k)...
Qed.


Corollary sat_mcnf_to_nnf :
  forall (phi : Nnf.t), Mcnf.satisfiable (Mcnfc.from_nnf phi) -> Nnf.satisfiable phi.
Proof with simpl; try autolia; auto.
  intros phi Hmcnf_sat.

  unfold Mcnf.satisfiable in Hmcnf_sat.
  destruct Hmcnf_sat as [W [R [M [w0 Hforce_mcnf]]]].

  unfold Nnf.satisfiable.
  exists W, R, M, w0.

  set (n := S (Nnf.max_atm phi)).

  apply mcnf_to_nnf_forces with (n:=n) (k:=S n)...
Qed.


(** Equisatisfiability of NNF and MCNF. *)
Theorem equisat_nnf :
  forall (phi : Nnf.t), Nnf.satisfiable phi <-> Mcnf.satisfiable (Mcnfc.from_nnf phi).
Proof.
  intro phi. split.
  - apply (sat_nnf_to_mcnf phi).
  - apply (sat_mcnf_to_nnf phi).
Qed.
