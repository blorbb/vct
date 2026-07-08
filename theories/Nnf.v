From CegarTableaux Require Lit Kripke Fml.
From CegarTableaux Require Import ImportStd.


(** A modal formula in negation normal form. *)
Inductive t : Set :=
  | Lit (l : Lit.t)
  | And (A B : t)
  | Or  (A B : t)
  | Box (A : t)
  | Dia (A : t).


Fixpoint force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  match phi with
  | Lit l   => Lit.force M w0 l
  | And A B => force M w0 A /\ force M w0 B
  | Or  A B => force M w0 A \/ force M w0 B
  | Box A   => forall w1, R w0 w1 -> force M w1 A
  | Dia A   => exists w1, R w0 w1 /\ force M w1 A
  end.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.


Definition unsatisfiable (phi : t) : Prop :=
  forall W R (M : @Kripke.t W R) (w0 : W), ~ force M w0 phi.


Definition as_lit (phi : t) : option Lit.t :=
  match phi with
  | Lit l => Some l
  | _ => None
  end.


Lemma as_lit_some_inv : forall phi l, as_lit phi = Some l <-> phi = (Nnf.Lit l).
Proof.
  intros phi l.
  destruct phi; cbn.
  1: split; intro; now inv_clear H.
  all: split; intro; discriminate.
Qed.


Lemma as_lit_none : forall {A} (phi : t) (f : Lit.t -> A) (other : A),
  as_lit phi = None ->
  (match phi with | Lit l => f l | _ => other end) = other.
Proof.
  intros * Hphi_none.
  destruct phi.
  1: discriminate.
  all: reflexivity.
Qed.

Ltac destruct_lit A :=
  let l := fresh "l" in
  let H := fresh in
  destruct (as_lit A) as [l|] eqn:H;
    [ rewrite as_lit_some_inv in H; repeat (rewrite H in *)
    | repeat (rewrite (as_lit_none A _ _ H) in *)].


Definition as_lit2 (A B : t) : option (Lit.t * Lit.t) :=
  match A, B with
  | Lit lA, Lit lB => Some (lA, lB)
  | _, _ => None
  end.

Lemma as_lit2_some_inv : forall A B lA lB,
  as_lit2 A B = Some (lA, lB) ->
  A = Lit lA /\ B = Lit lB.
Proof.
  intros * Hlits.
  destruct A; destruct B; try easy.
  cbn in Hlits. now inv_clear Hlits.
Qed.

Lemma as_lit2_none : forall {X} (A B : t) (f : Lit.t -> Lit.t -> X) (other : X),
  as_lit2 A B = None ->
  (match A, B with | Lit lA, Lit lB => f lA lB | _, _ => other end) = other.
Proof.
  intros * Hnone.
  destruct A; destruct B; easy.
Qed.

Ltac destruct_lit2 A B :=
  let lA := fresh "l" A in
  let lB := fresh "l" B in
  let H := fresh in
  let HA := fresh "H" A in
  let HB := fresh "H" B in
  destruct (as_lit2 A B) as [[lA lB] |] eqn:H;
    [ apply as_lit2_some_inv in H as [HA HB];
      repeat (rewrite HA in *);
      repeat (rewrite HB in *)
    | repeat (rewrite (as_lit2_none A B _ _ H) in *)].


Section Conversion.
  Fixpoint negate (phi : t) : t :=
    match phi with
    | Lit l   => Lit (Lit.negate l)
    | And A B => Or  (negate A) (negate B)
    | Or  A B => And (negate A) (negate B)
    | Box A   => Dia (negate A)
    | Dia A   => Box (negate A)
    end.


  Fixpoint from_fml (phi : Fml.t) : t :=
    match phi with
    | Fml.Var  p   => Lit (Lit.Pos p)
    | Fml.Neg  A   => negate (from_fml A)
    | Fml.And  A B => And (from_fml A) (from_fml B)
    | Fml.Or   A B => Or  (from_fml A) (from_fml B)
    | Fml.Impl A B => Or  (negate (from_fml A)) (from_fml B)
    | Fml.Box  A   => Box (from_fml A)
    | Fml.Dia  A   => Dia (from_fml A)
    end.
End Conversion.


(** Logical equivalence of the [from_fml] conversion. *)
Section Correctness.
  Theorem force_negate_iff_not_force {W} {R} (M : @Kripke.t W R) :
    forall w0 phi, force M w0 (negate phi) <-> ~ force M w0 phi.
  Proof.
    intros w0 phi.
    revert w0. (* make the induction hypothesis on 'forall w0' *)
    induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ]; intro w0; simpl.
    (* literals *)
    - destruct l.
      + reflexivity.
      + simpl. tauto.
    (* And, Or *)
    - rewrite IHA. rewrite IHB. tauto.
    - rewrite IHA. rewrite IHB. tauto.
    (* Box *)
    - split.
      (* exists w1 : not A sat -> not all neighbours force *)
      + intros Hexists Hforall.
        destruct Hexists as [w1 [HR_w1 Hforce]].
        specialize (Hforall w1 HR_w1). (* remove the forall *)
        apply IHA in Hforce.
        contradiction.
      (* not all neighbours force -> exists w1 : not A sat *)
      + intros Hforall.
        apply not_all_ex_not in Hforall.
        destruct Hforall as [w1 Himpl].
        apply not_imply_elim in Himpl as HR_w1.
        apply not_imply_elim2 in Himpl as Hforce.
        exists w1.
        split.
        * apply HR_w1.
        * apply IHA. apply Hforce.
    (* Dia *)
    - split.
      (* all neighbours force not A -> doesn't exist neighbour : force A *)
      + intros Hforall Hexists.
        destruct Hexists as [w1 [HR_w1 Hforce]].
        specialize (Hforall w1 HR_w1).
        apply IHA in Hforall.
        contradiction.
      + intros Hexists w1 HR_w1.
        apply not_ex_all_not with (n := w1) in Hexists.
        apply not_and_or in Hexists.
        destruct Hexists as [contra | not_nnf].
        * contradiction.
        * apply IHA. exact not_nnf.
  Qed.


  Theorem equiv_fml :
    forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : Fml.t),
    Fml.force M w0 phi <-> force M w0 (from_fml phi).
  Proof.
    intros W R M w0 phi. revert w0.
    induction phi as
      [ p
      | A IHA
      | A IHA B IHB
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ]; intro w0; simpl.
    (* Var p *)
    - tauto.
    (* Neg fml *)
    - rewrite force_negate_iff_not_force. rewrite IHA. reflexivity.
    (* A /\ B *)
    - rewrite IHA. rewrite IHB. reflexivity.
    (* A \/ B *)
    - rewrite IHA. rewrite IHB. reflexivity.
    (* A -> B *)
    - rewrite IHA. rewrite IHB. rewrite force_negate_iff_not_force. tauto.
    (* []A *)
    - setoid_rewrite IHA. reflexivity.
    (* <>A *)
    - setoid_rewrite IHA. reflexivity.
  Qed.


  Corollary equisat_fml :
    forall (phi : Fml.t), Fml.satisfiable phi <-> Nnf.satisfiable (from_fml phi).
  Proof.
    intro phi. split.
    - intros [W [M [R [w0 Hforce]]]]. exists W, M, R, w0. 
      now apply equiv_fml.
    - intros [W [M [R [w0 Hforce]]]]. exists W, M, R, w0. 
      now apply equiv_fml.
  Qed.
End Correctness.


(** Definitions and theorems relating to the structure of an NNF formula. *)
Section Range.
  Fixpoint max_atm (phi : t) : nat :=
    match phi with
    | Lit l => Lit.atm l
    | And A B => Nat.max (max_atm A) (max_atm B)
    | Or  A B => Nat.max (max_atm A) (max_atm B)
    | Box A   => max_atm A
    | Dia A   => max_atm A
    end.

  Fixpoint atm_in (p : nat) (phi : t) : Prop :=
    match phi with
    | Lit l => p = Lit.atm l
    | And A B => atm_in p A \/ atm_in p B
    | Or  A B => atm_in p A \/ atm_in p B
    | Box A   => atm_in p A
    | Dia A   => atm_in p A
    end.


  Corollary atm_in_nnf_atm :
    forall (l : Lit.t), atm_in (Lit.atm l) (Lit l).
  Proof.
    intros l. destruct l; reflexivity.
  Qed.


  Theorem atm_le_max : forall (phi : t) (p : nat),
    atm_in p phi -> p <= (max_atm phi).
  Proof.
    intros phi p Hx_in_nnf.

    induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ].
    - simpl in *. destruct l; lia.
    - simpl in *. destruct Hx_in_nnf.
      + forward IHA by assumption. lia.
      + forward IHB by assumption. lia.
    - simpl in *. destruct Hx_in_nnf.
      + forward IHA by assumption. lia.
      + forward IHB by assumption. lia.
    - simpl in *. forward IHA by assumption. lia.
    - simpl in *. forward IHA by assumption. lia.
  Qed.


  Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
    forall (w0 : W) (p : nat), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).

  (** Makes some proofs in mcnf a bit easier.

      Agree on phi implies agree on subformulae of phi *)
  Corollary agree_l {W} {R} {M M' : @Kripke.t W R} (l r : t) :
    agree (And l r) M M' -> agree l M M'.
  Proof.
    intro Hagree.
    unfold agree in *.
    intros w0 p Hp_in_left.
    apply Hagree. simpl. now left.
  Qed.

  Corollary agree_r {W} {R} {M M' : @Kripke.t W R} (l r : t) :
    agree (And l r) M M' -> agree r M M'.
  Proof.
    intro Hagree.
    unfold agree in *.
    intros w0 p Hp_in_right.
    apply Hagree. simpl. now right.
  Qed.


  Theorem meaningful_valuations :
    forall {W} {R} (M M' : @Kripke.t W R) (w0 : W) (phi : t),
      agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
  Proof with simpl; auto.
    intros W R M M' w0 phi Hagree. revert w0 Hagree.
    induction phi as
      [ l
      | A IHA B IHB
      | A IHA B IHB
      | A IHA
      | A IHA
      ]; intros w0 Hagree.
    (* literal base case *)
    - split.
      + intro HMforce.
        set (p := Lit.atm l).
        assert (Hin : atm_in p (Lit l)) by apply atm_in_nnf_atm.
        specialize (Hagree w0 p Hin).
        simpl in *.
        unfold Lit.force in *.
        (* (~) valuation M' w0 p0 = (~) valuation m w0 p *)
        destruct l; subst p; rewrite <- Hagree; exact HMforce.
      + intro HMforce.
        set (p := Lit.atm l).
        assert (Hin : atm_in p (Lit l)) by apply atm_in_nnf_atm.
        specialize (Hagree w0 p Hin).
        simpl in *.
        unfold Lit.force in *.
        (* (~) valuation M' w0 p0 = (~) valuation m w0 p *)
        destruct l; subst p; rewrite -> Hagree; exact HMforce.
    (* And case *)
    - split.
      (* M forces -> M' forces *)
      + intro HMforce.
        simpl. split.
        { (* forces A *)
          apply IHA.
          - intros w0' p Hin.
            apply Hagree. simpl. now left.
          - apply HMforce.
        }
        { (* forces B *)
          apply IHB.
          - intros w0' p Hin.
            apply Hagree. simpl. now right.
          - apply HMforce.
        }
      (* M' forces -> M forces *)
      + intro HM'force.
        simpl. split.
        { (* forces A *)
          apply IHA.
          - intros w0' p Hin.
            apply Hagree. simpl. now left.
          - apply HM'force.
        }
        { (* forces B *)
          apply IHB.
          - intros w0' p Hin.
            apply Hagree. simpl. now right.
          - apply HM'force.
        }
    (* Or case *)
    - split.
      (* M forces -> M' forces *)
      + intro HMforce.
        simpl. simpl in HMforce. destruct HMforce as [Hforce_a|Hforce_b].
        { (* forces A *)
          left. apply IHA.
          - intros w0' p Hin.
            apply Hagree. simpl. now left.
          - exact Hforce_a.
        }
        { (* forces B *)
          right. apply IHB.
          - intros w0' p Hin.
            apply Hagree. simpl. now right.
          - exact Hforce_b.
        }
      (* M' forces -> M forces *)
      + intro HM'force.
        simpl. simpl in HM'force. destruct HM'force as [Hforce_a|Hforce_b].
        { (* forces A *)
          left. apply IHA...
          intros w0' p Hin.
          apply Hagree. simpl. now left.
        }
        { (* forces B *)
          right. apply IHB...
          intros w0' p Hin.
          apply Hagree. simpl. now right.
        }
    (* Box case *)
    - simpl. split.
      + intros HMforce w1 HR_w1.
        apply IHA...
      + intros HM'force w1 HR_w1.
        apply IHA...
    - simpl. split.
      + intros HMforce.
        destruct HMforce as [w1 [HR_w1 Hforce]].
        exists w1.
        split...
        apply IHA...

      + intros HM'force.
        destruct HM'force as [w1 [HR_w1 Hforce]].
        exists w1.
        split...
        apply IHA...
  Qed.
End Range.
