From CegarTableaux Require Import ImportStd.


(** Valuation represented as a list of forced atoms. *)
Definition t := list nat.


(** Every atom must appear at most once. *)
Definition clash_free (V : t) := List.NoDup V.


Lemma clash_free_nil : clash_free [].
Proof. unfold clash_free. apply NoDup_nil. Qed.


Definition forces_atm (V : t) (p : nat) : bool := List.existsb (Nat.eqb p) V.


(** Set-equality of valuations *)
Definition eq (a b : t) : Prop :=
  Permutation a b.
Hint Unfold eq : ct.

(* coq can auto solve these *)
Global Instance eq_equivalence : Equivalence eq := {}.


(** These 2 are unused but might be helpful later. *)

Lemma eq_clash_free : forall (V V' : t), eq V V' -> clash_free V -> clash_free V'.
Proof with auto.
  intros V V' Heq Hcf.
  unfold clash_free, eq in *.
  eapply Permutation_NoDup.
  - exact Heq.
  - assumption.
Qed.

Lemma eq_in : forall (p : nat) (V V' : t), eq V V' -> In p V <-> In p V'.
Proof with auto.
  intros p V V' Heq.
  unfold eq in Heq.
  split.
  - apply Permutation_in...
  - apply Permutation_in. apply Permutation_sym...
Qed.


(** Generate every valuation from a set of atoms. *)
Section AllValuations.
  Fixpoint every_valuation_of_atms (atms : list nat) : list t :=
    match atms with
    | [] => [[]]
    | atm :: atms' =>
      let every_atms' := every_valuation_of_atms atms' in
      every_atms' ++ List.map (cons atm) every_atms'
    end.


  Definition val_in_vals (V : t) (vals : list t) : Prop :=
    InA eq V vals.


  (* TODO: rename this lemma. *)
  (** Every valuation is a subset of the input atms. *)
  Lemma every_valuation_exact_atms : forall (atms : list nat),
    List.Forall (fun V => List.incl V atms) (every_valuation_of_atms atms).
  Proof with try easy; auto with datatypes.
    setoid_rewrite List.Forall_forall.
    intros atms.

    induction atms as [|head tail IHtail].
    - intros V Hval_in.
      cbn in Hval_in.
      destruct Hval_in as [Hval_nil | F]... subst V...
    - intros V Hval_in_vals.

      cbn in *. apply List.in_app_iff in Hval_in_vals.
      destruct Hval_in_vals as [Hin_t | Hin_ht]...
      apply List.in_map_iff in Hin_ht.
      destruct Hin_ht as [v' [Hv'_is_tail Hv'_in_et]].
      subst V...
  Qed.


  Lemma every_valuation_clash_free : forall (atms : list nat),
    List.NoDup atms ->
    List.Forall clash_free (every_valuation_of_atms atms).
  Proof with try easy; auto with datatypes ct.
    intros atms Hnodup.
    induction Hnodup as [| head tail Hhead_nin Hnd IH].
    - cbn. apply List.Forall_forall.
      intros V Hval_nil.
      cbn in Hval_nil. destruct Hval_nil as [Hval_nil | F]...
      subst V. apply clash_free_nil.
    - rewrite List.Forall_forall in *.
      intros V Hval_in.
      cbn in Hval_in. apply List.in_app_iff in Hval_in.
      destruct Hval_in as [Hval_in_t | Hval_in_ht].
      + apply IH...
      + apply List.in_map_iff in Hval_in_ht as [t' [Ht' Ht'_in]]. subst V.
        unfold clash_free. apply NoDup_cons.
        * intro Hhead_in. apply Hhead_nin.
          pose proof (every_valuation_exact_atms tail) as Hatms_of_val.
          rewrite List.Forall_forall in Hatms_of_val.
          apply (Hatms_of_val t')...
        * apply IH...
  Qed.


  Lemma atms_in_ev_atms : forall (atms : list nat),
    List.In atms (every_valuation_of_atms atms).
  Proof with auto.
    intro atms. induction atms as [| h t IH].
    - cbn. now left.
    - cbn. apply List.in_app_iff. right.
      apply List.in_map_iff.
      exists t. split...
  Qed.


  Lemma val_with_atms_in_every_val :
    forall atms V,
      clash_free V ->
      List.incl V atms ->
      val_in_vals V (every_valuation_of_atms atms).
  Proof with auto with typeclass_instances datatypes ct.
    intros atms. induction atms as [|h t IH]; intros V Hcf Hincl.
    { apply List.incl_l_nil in Hincl. subst. cbn. now apply InA_singleton. }
    unfold val_in_vals in *.
    destruct (in_dec Nat.eq_dec h V) as [Hin | Hnin].

    (* h in V *)
    - apply in_split in Hin. destruct Hin as [l1 [l2 Hval]].
      unfold clash_free in *. subst V.
      apply NoDup_remove in Hcf as [Hnd_l1l2 Hh_nin_l1l2].
      assert (incl (l1++l2) t) as Hl1l2_incl. {
        eapply incl_Add_inv.
        - exact Hh_nin_l1l2.
        - rewrite incl_middle. exact Hincl.
        - apply Add_head.
      }
      specialize (IH (l1++l2) Hnd_l1l2 Hl1l2_incl).
      rewrite InA_alt in *.
      destruct IH as [l1l2' [Hl1l2'_eq Hl1l2'_in]].
      exists (h :: l1l2'). split.
      + unfold eq in *.
        eapply perm_trans.
        * symmetry. apply Permutation_middle.
        * now apply perm_skip.
      + cbn. apply List.in_app_iff. right.
        apply List.in_map_iff. exists l1l2'...

  (* h not in V *)
  - cbn. apply InA_app_iff. left.
    apply IH...
    apply incl_Add_inv with (a := h) (v := h::t)... apply Add_head.
  Qed.


  Lemma every_valuation_perm : forall (atms atms' : list nat),
    Permutation atms atms' ->
    PermutationA eq (every_valuation_of_atms atms) (every_valuation_of_atms atms').
  Proof with try easy; auto with *.
    intros atms atms' Hperm.
    induction Hperm.
    - reflexivity.
    - cbn. apply PermutationA_app... apply PermutationA_map...
    - cbn.
      set (vals := (every_valuation_of_atms l)).
      (* remove the vals ++ ... *)
      repeat rewrite List.map_app.
      repeat rewrite <- List.app_assoc.
      apply PermutationA_app_head...
      (* split into (map ++ map) ++ (map _ (map ..)) *)
      repeat rewrite List.app_assoc.
      apply PermutationA_app...
      + apply PermutationA_app_comm...
      + induction vals as [|v vals IHvals]...
        cbn.
        apply PermutationA_cons. { apply perm_swap. } apply IHvals.
    - apply (
        @permA_trans
          t
          eq
          (every_valuation_of_atms l)
          (every_valuation_of_atms l')
          (every_valuation_of_atms l'')
      )...
  Qed.


  Lemma bind_new_atm_unique : forall (vals : list t) (p : nat),
    NoDupA eq vals ->
    (* p is not in vals *)
    (forall v, List.In v vals -> ~ List.In p v) ->
    NoDupA eq (vals ++ map (cons p) vals).
  Proof with try easy; auto with typeclass_instances datatypes ct.
    intros vals p Hnodup Hatm_nin_vals.

    induction Hnodup as [|v vals Hv_nin_vals Hnodup_vals IHnodup]...
    cbn. constructor.

    - intro H. apply InA_app in H. rewrite InA_cons in H.
      destruct H as [Hv_in_vals | [Hv_eq_pv | Hv_in_mapvals]].
      + contradiction.
      + unfold eq in Hv_eq_pv. symmetry in Hv_eq_pv.
        apply Permutation_head_ne in Hv_eq_pv. contradiction.
      + rewrite InA_altdef in Hv_in_mapvals. rewrite Exists_exists in Hv_in_mapvals.
        destruct Hv_in_mapvals as [v' [Hv'_in Hvv']].
        apply (Hatm_nin_vals v).
        * apply in_eq.
        * apply Permutation_in with (l := v')...
          apply in_map_iff in Hv'_in.
          destruct Hv'_in as [tl [Htl_eq _]]. subst v'.
          apply in_eq.

    - apply NoDupA_swap_iff... apply NoDupA_cons.
      2: { apply IHnodup. intros. apply Hatm_nin_vals. now right. }

      intro H. apply InA_app in H as [Hpv_in_vals | Hpv_in_mapvals].
      + apply InA_alt in Hpv_in_vals as [pv [Hpv_eq Hpv_in_vals]].
        apply (Hatm_nin_vals pv).
        * now right.
        * apply Permutation_in with (l := p::v)...
      + apply InA_alt in Hpv_in_mapvals as [pv [Hpv_eq Hpv_in_mapvals]].
        apply in_map_iff in Hpv_in_mapvals as [v' [Hv'_eq Hv'_in]].
        subst pv. apply Hv_nin_vals.
        apply InA_eqA with (x := v')...
        * unfold eq in *. eapply Permutation_cons_inv. symmetry. exact Hpv_eq.
        * apply In_InA...
  Qed.


  Lemma every_valuation_unique : forall (atms : list nat),
    List.NoDup atms ->
    NoDupA eq (every_valuation_of_atms atms).
  Proof with try easy; auto with typeclass_instances.
    intros atms Hnd.

    induction Hnd as [|h t Hh_nin_t Hnd_t IHnd]; cbn.
    { apply NoDupA_singleton. }

    set (ev_t := every_valuation_of_atms t) in *.
    apply bind_new_atm_unique...
    intros v Hv_in Hh_in. apply Hh_nin_t.
    pose proof (every_valuation_exact_atms t) as H.
    rewrite List.Forall_forall in H.
    apply H with (x := v)...
  Qed.
End AllValuations.

Global Hint Resolve every_valuation_exact_atms every_valuation_clash_free atms_in_ev_atms val_with_atms_in_every_val every_valuation_perm every_valuation_unique : ct.