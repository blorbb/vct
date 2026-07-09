From CegarTableaux Require Import ImportStd.
From CegarTableaux.Solver Require Import McnfExt.
From CegarTableaux.Solver Require Derivation Spec.
From CegarTableaux Require Cnf.

(** Some basic properties about the solutions returned by [tableau] and [tableau_jumps].  *)

Lemma tableau_deriv_core : forall A s0 mc0 core deriv,
  Spec.Solution.Unsat core deriv = Spec.tableau A s0 mc0 ->
  core = Derivation.get_core deriv.
Proof.
  intros *. intro Hunsat.
  funelim (Spec.tableau A s0 mc0); rewrite <- Heqcall in Hunsat.
  - inversion_clear Hunsat. reflexivity.
  - discriminate.
  - discriminate.
  - destruct (Spec.tableau _ _ _).
    + discriminate.
    + inversion_clear Hunsat. cbn. now apply H.
Qed.

Lemma jump_failed_dia : forall V l0 mc1 failed_dia core deriv,
  Spec.JumpSolution.Unsat failed_dia core deriv = Spec.tableau_jumps V l0 mc1 (Spec.next_tableau mc1) ->
  List.In failed_dia (Lclauses.dias l0).
Proof.
  intros *. intro Hunsat.
  funelim (Spec.tableau_jumps V l0 mc1 (Spec.next_tableau mc1));
    cbn in *; rewrite <- Heqcall in Hunsat.
  - discriminate.
  - right. eapply H. exact Hunsat.
  - left. now inversion_clear Hunsat.
  - discriminate.
  - right. inversion_clear Hunsat. eapply Hind. symmetry. exact Heq.
Qed.

Lemma jump_deriv_core : forall V l0 mc1 failed_dia core deriv,
  Spec.JumpSolution.Unsat failed_dia core deriv = Spec.tableau_jumps V l0 mc1 (Spec.next_tableau mc1) ->
  core = Derivation.get_core deriv.
Proof.
  intros *. intros Hunsat.
  funelim (Spec.tableau_jumps V l0 mc1 (Spec.next_tableau mc1));
    cbn in *; rewrite <- Heqcall in Hunsat.
  - discriminate.
  - eapply H. exact Hunsat.
  - inversion_clear Hunsat.
    eapply tableau_deriv_core. symmetry. exact Heq.
  - discriminate.
  - inversion_clear Hunsat. eapply Hind. symmetry. exact Heq.
Qed.

(** * [Derivation.conds] proofs *)

Lemma tableau_jumps_deriv : forall V l0 mc1 failed_dia core deriv,
  Spec.JumpSolution.Unsat failed_dia core deriv = Spec.tableau_jumps V l0 mc1 (Spec.next_tableau mc1) ->
  (forall A' core deriv,
    Spec.Solution.Unsat core deriv = Spec.next_tableau mc1 A' ->
    Derivation.conds mc1 A' deriv) ->
  Derivation.conds mc1 (snd failed_dia :: fired_boxes (l0::mc1) V) deriv.
Proof.
  intros * Hunsat IHnt.
  funelim (Spec.tableau_jumps V l0 mc1 (Spec.next_tableau mc1)); rewrite <- Heqcall in Hunsat.
  - discriminate.
  - eapply H.
    + exact Hunsat.
    + exact IHnt.
  - inversion_clear Hunsat. cbn. unfold "|>" in Heq.
    eapply IHnt. symmetry. exact Heq.
  - discriminate.
  - inversion_clear Hunsat. eapply Hind.
    + symmetry. exact Heq.
    + exact IHnt.
Qed.

Lemma tableau_deriv : forall A s0 mc0 core deriv,
  Spec.Solution.Unsat core deriv = Spec.tableau A s0 mc0 ->
  s0 = CplSolver.make_with_clauses (first_cpls mc0) ->
  Derivation.conds mc0 A deriv.
Proof with auto.
  intros *. intros Hunsat Hs0. funelim (Spec.tableau A s0 mc0).
  - rewrite <- Heqcall in Hunsat. injection Hunsat as _ Hderiv. subst.
    apply Derivation.IdCond. now unfold cpl_solve.
  - cbn in *. rewrite <- Heqcall in Hunsat. discriminate.
  - cbn in *. rewrite <- Heqcall in Hunsat. discriminate.
  - rewrite <- Heqcall in Hunsat.
    destruct (Spec.tableau _ _ _); try discriminate.
    injection Hunsat as _ Hderiv. subst.
    apply Derivation.JumpRestartCond.
    + auto.
    + unfold first_dias. cbn. eauto using jump_failed_dia.
    + cbn. eauto using Spec.jump_c_forced.
    + apply tableau_jumps_deriv with (core := jump_core).
      * symmetry. apply Hj_eq.
      * intros. apply (Hind A' core1 deriv)...
    + cbn [first_ctx fst]. erewrite <- jump_deriv_core.
      2: { symmetry. exact Hj_eq. }
      apply H with (core := core0)...
Qed.

(** The derivation conditions are held for the [solve_*] functions. *)
Corollary solve_mcnf_deriv : forall phi core deriv,
  Spec.Solution.Unsat core deriv = Spec.solve_mcnf phi ->
  Derivation.conds phi [] deriv.
Proof.
  intros *. intros Hunsat.
  eapply tableau_deriv.
  - exact Hunsat.
  - reflexivity.
Qed.

Corollary solve_fml_deriv : forall phi core deriv,
  Spec.Solution.Unsat core deriv = Spec.solve_fml phi ->
  Derivation.conds (phi |> Nnf.from_fml |> Mcnf.from_nnf) [] deriv.
Proof.
  intros. eapply solve_mcnf_deriv. exact H.
Qed.


(** * Soundness *)

(** A derivation that satisfies [Derivation.conds] is sound. *)

(** Some helpers to simplify unsat goals. *)

Lemma cnf_unsat_subset : forall phi, Cnf.unsatisfiable (first_cpls phi) -> Mcnf.unsatisfiable phi.
Proof.
  intros phi. induction phi as [|l0 mc1].
  - cbn. intros Hcnf_unsat Hm_sat.
    unfold Cnf.unsatisfiable, Cnf.satisfiable in Hcnf_unsat.
    unfold Mcnf.satisfiable in Hm_sat.
    destruct Hm_sat as [W [R [M [mc0 _]]]].
    apply Hcnf_unsat.
    exists W, R, M, mc0. cbn.
    now apply List.Forall_nil_iff.
  - cbn. intros Hcnf_unsat Hm_sat.
    unfold Cnf.unsatisfiable, Cnf.satisfiable in Hcnf_unsat.
    unfold Mcnf.satisfiable in Hm_sat.
    destruct Hm_sat as [W [R [M [mc0 Hforce]]]].
    apply Hcnf_unsat.
    exists W, R, M, mc0.
    cbn in Hforce.
    do 2 apply proj1 in Hforce. exact Hforce.
Qed.


Lemma Mcnf_cpls : forall {cpls cpls' boxes dias mc1},
  Mcnf.unsatisfiable (Lclauses.make cpls boxes dias :: mc1) ->
  (forall W R (M : @Kripke.t W R) mc0, Cnf.force M mc0 cpls' -> Cnf.force M mc0 cpls) ->
  Mcnf.unsatisfiable (Lclauses.make cpls' boxes dias :: mc1).
Proof.
  intros * Hunsat Himpl [W [R [M [mc0 Hforce]]]]. apply Hunsat.
  exists W, R, M, mc0. cbn in Hforce |- *. auto with solve_subterm.
Qed.

(** ** Resolution *)

(** Lemmas to prove that [phi /\ x] and [phi /\ ~x] being unsatisfiable implies
    that [phi] is unsatisfiable. *)

(* TODO: this is really messy. clean up. *)
Lemma not_all_some_true : forall {W} {R} (M : @Kripke.t W R) mc0 A,
  ~ Cnf.force M mc0 (Cnf.from_assumptions A) ->
  CplClause.force M mc0 (List.map Lit.negate A).
Proof with try easy; auto.
  intros * Hforce_A.
  cbn in *.
  rewrite <- Exists_Forall_neg in Hforce_A. 2: { intro; apply classic. }
  rewrite List.Exists_exists in Hforce_A.
  destruct Hforce_A as [cl [Hcl_in Hnforce]].
  unfold Cnf.from_assumptions in Hcl_in.
  rewrite List.in_map_iff in Hcl_in. destruct Hcl_in as [l [Hl_cl Hl_in]]. subst.
  exists (Lit.negate l). split.
  - now apply List.in_map.
  - cbn in *.
    apply not_ex_all_not with (n := l) in Hnforce.
    apply Lit.not_force_negate...
Qed.

(** Weird definition to fit the contexts this is used in. *)
Lemma force_first_cpls : forall {W} {R} {M : @Kripke.t W R} {w0} mc0 cpls boxes dias,
  Mcnf.force M w0 mc0 ->
  first_ctx mc0 = Lclauses.make cpls boxes dias ->
  Cnf.force M w0 cpls.
Proof.
  intros * Hforce Hl0. destruct mc0 as [|l0 mc1]; cbn in *.
  - inversion_clear Hl0. auto.
  - subst l0; cbn in *. tauto.
Qed.

Lemma force_new_cpls : forall {W} {R} {M : @Kripke.t W R} {w0} mc0 cpls' cpls boxes dias,
  first_ctx mc0 = Lclauses.make cpls boxes dias ->
  Mcnf.force M w0 mc0 ->
  Cnf.force M w0 cpls' ->
  Mcnf.force M w0 ((Lclauses.make (cpls' ++ cpls) boxes dias) :: next_ctx mc0).
Proof.
  intros * Hl0_eq Hforce_w0 Hforce_cpls'. destruct mc0 as [|l0 mc1].
  - cbn in *. inversion_clear Hl0_eq. intuition.
    apply Forall_app; auto.
  - cbn in *; subst; cbn in *. intuition.
    apply Forall_app; auto.
Qed.

Lemma Mcnf_resolution : forall mc0 (A : list Lit.t),
  Mcnf.unsatisfiable (add_assumptions mc0 A) ->
  Mcnf.unsatisfiable (add_neg_assumptions mc0 A) ->
  Mcnf.unsatisfiable mc0.
Proof with try easy; auto.
  intros mc0 cs Hcs Hncs [W [R [M [w Hforce]]]].
  apply Hncs. exists W, R, M, w.
  (* rewrite unsat_force in Hcs. *)
  cbn. repeat split; try solve [destruct mc0; cbn in *; intuition].
  destruct (first_ctx mc0) as [cpls boxes dias] eqn:Hl0_eq; cbn.
  apply List.Forall_cons.
  - cbn in *. rewrite Hl0_eq in *; cbn in *.
    apply not_all_some_true. intro Hforce_cnf.
    apply Hcs. exists W, R, M, w. apply force_new_cpls...
  - apply (force_first_cpls mc0 cpls boxes dias)...
Qed.

Corollary Mcnf_resolution_cs : forall mc0 (cs : list nat),
  Mcnf.unsatisfiable (add_conflict_set mc0 cs) ->
  Mcnf.unsatisfiable (add_assumptions mc0 (List.map Lit.Pos cs)) ->
  Mcnf.unsatisfiable mc0.
Proof.
  intros * Hcs HA. apply Mcnf_resolution with (A := (List.map Lit.Pos cs)).
  - easy.
  - cbn in *. rewrite List.map_map. cbn. apply Hcs.
Qed.

(** ** Soundness of derivation *)

Lemma cpls_of_add_assumptions : forall mc0 A,
  first_cpls (add_assumptions mc0 A) = Cnf.from_assumptions A ++ first_cpls mc0.
Proof.
  intros. destruct mc0.
  - cbn. now rewrite List.app_nil_r.
  - destruct t; cbn. reflexivity.
Qed.

Lemma deriv_core_incl_A : forall mc0 A deriv,
  Derivation.conds mc0 A deriv ->
  List.incl (Derivation.get_core deriv) A.
Proof.
  intros * Hconds.
  induction Hconds as
    [mc0 A core Hunsat
    | mc0 A V failed_dia jump_deriv rs_deriv Hsat Hdia_in Hforce_c Hjump IHjump Hrs IHrs].
  - cbn. eapply CplSolver.core_subset_assumptions. exact Hunsat.
  - cbn. exact IHrs.
Qed.


Theorem deriv_sound : forall mc0 A deriv,
  Derivation.conds mc0 A deriv ->
  Mcnf.unsatisfiable (add_assumptions mc0 (Derivation.get_core deriv)).
Proof with cbn in *; try easy; auto with datatypes ct typeclass_instances.
  intros mc0 A deriv Hconds.
  induction Hconds as
    [mc0 A core Hunsat
    | mc0 A V failed_dia jump_deriv rs_deriv Hsat Hdia_in Hforce_c Hjump IHjump Hrs IHrs].
  (* CNF subset is unsatisfiable. *)
  - apply cnf_unsat_subset.

    rewrite cpls_of_add_assumptions.
    rewrite <- (CplSolver.clauses_of_make_with_clauses (first_cpls mc0)).
    unfold cpl_solve in Hunsat. set (s0 := CplSolver.make_with_clauses (first_cpls mc0)) in *.
    apply (CplSolver.solution_soundness s0 A core)...

  (* mc0 /\ cs and mc0 /\ ~cs are both unsatisfiable.
     mc0 /\ cs is from IHjump, but need to go up a modal context.
     mc0 /\ ~cs is from IHrs. *)
  - destruct failed_dia as [c d]; cbn [fst snd] in *.
    cbn [Derivation.get_core].
    set (cs := conflict_set_of mc0 V c (Derivation.get_core jump_deriv)) in *.
    apply Mcnf_resolution_cs with (cs := cs).
    (* mc0 /\ ~cs *)
    + clear -IHrs. fold cs.
      destruct (first_ctx mc0) as [cpls boxes dias] eqn:Hl0_eq.
      apply (Mcnf_cpls IHrs).
      intros W R M w0 Hforce.
      rewrite Cnf.permutation_force. { exact Hforce. }
      symmetry. cbn. apply Permutation_middle.
    (* mc0 /\ cs *)
    (* TODO: clean up simplification and core proof parts. *)
    + clear IHrs.
      destruct (first_ctx mc0) as [cpls boxes dias] eqn:Hl0_eq.
      set (mc1 := next_ctx mc0) in *.
      pose proof (deriv_core_incl_A mc1 (d::fired_boxes mc0 V) jump_deriv Hjump) as Hcore_incl.

      intros Hmsat. apply IHjump.

      destruct Hmsat as [W [R [M [mc1M Hmc1M]]]].
      cbn in Hmc1M. destruct Hmc1M as [[Hf_cpls1 [Hf_boxes1 Hf_dias1]] Hf_w2].
      unfold first_dias in Hdia_in. rewrite Hl0_eq in *. cbn in *.

      (* get the adjacent dia world that must be forced *)
      rewrite List.Forall_forall in Hf_cpls1, Hf_boxes1, Hf_dias1.
      specialize (Hf_dias1 (c,d)).
      unfold first_dias in Hdia_in. forward Hf_dias1 by exact Hdia_in.
      unfold DiaClause.force in Hf_dias1.
      forward Hf_dias1. {
        cbn. specialize (Hf_cpls1 [Lit.Pos c]).
        forward Hf_cpls1 by now left.
        cbn in Hf_cpls1. destruct Hf_cpls1 as [c' [Hc' Hforce_c']].
        destruct Hc'... subst c'.
        cbn in Hforce_c'. assumption.
      }

      destruct Hf_dias1 as [w2M [Hw2R Hw2_force]]. cbn in Hw2_force.
      exists W, R, M, w2M.

      (* assumptions must be forced by boxes *)
      destruct (first_ctx mc1) as [cpls1 boxes1 dias1] eqn:Hl1_eq; cbn in *.
      apply (force_new_cpls mc1)...
      rewrite List.Forall_forall.
      intros cl Hcl_in.
      unfold Cnf.from_assumptions in Hcl_in.
      rewrite List.in_map_iff in Hcl_in. destruct Hcl_in as [l [Hl_cl Hl_in]]. subst cl.
      cbn. exists l. intuition.
      apply Hcore_incl in Hl_in as Hl_in_db. destruct Hl_in_db as [Hld | Hlb].
      * subst. cbn. auto.
      * rewrite List.in_map_iff in Hlb. destruct Hlb as [(a, b) [Hab Hab_in]]; cbn in *; subst.
        rewrite List.filter_In in Hab_in. destruct Hab_in as [Hab_in Hforce_a].
        apply (Hf_boxes1 (a,l))... { unfold first_boxes in Hab_in; rewrite Hl0_eq in Hab_in; cbn in Hab_in. easy. }
        specialize (Hf_cpls1 [Lit.Pos a]).
        forward Hf_cpls1. {
          right. apply List.in_app_iff. left.
          apply List.in_map_iff. exists (Lit.Pos a). split...
          apply List.in_map_iff. exists a. split...
          apply List.in_map_iff. exists (a, l). split...
          repeat rewrite List.filter_In. repeat split.
          - assumption.
          - cbn. exact Hforce_a.
          - rewrite List.existsb_exists. exists l.
            split... apply Lit.eqb_eq...
        }
        destruct Hf_cpls1 as [a' [Ha'_eq Hforce_a']].
        cbn in Ha'_eq. destruct Ha'_eq... subst.
        cbn in Hforce_a'. exact Hforce_a'.
Qed.

(** ** Soundness of tableau *)


Corollary solve_mcnf_sound : forall mc0,
  Spec.Solution.is_sat (Spec.solve_mcnf mc0) = false ->
  Mcnf.unsatisfiable mc0.
Proof with try easy.
  intros mc0 Hunsat. destruct (Spec.solve_mcnf mc0) eqn:Hsolve...
  clear Hunsat.
  pose proof (solve_mcnf_deriv mc0 core deriv (eq_sym Hsolve)) as Hconds.
  pose proof (deriv_sound mc0 [] deriv Hconds) as Hunsat.
  assert (Derivation.get_core deriv = []) as Hderiv. {
    apply incl_l_nil. apply deriv_core_incl_A with (mc0 := mc0)...
  } rewrite Hderiv in Hunsat.
  intro Hsat. apply Hunsat.
  destruct Hsat as [W [R [M [w0 Hforce]]]]. exists W, R, M, w0.
  destruct mc0 as [|l0 mc1].
  - cbn. intuition.
  - cbn in Hforce |- *. intuition.
Qed.


Corollary solve_fml_sound : forall phi,
  Spec.Solution.is_sat (Spec.solve_fml phi) = false ->
  Fml.unsatisfiable phi.
Proof.
  intros phi Hunsat Hsat.
  rewrite Nnf.equisat_fml in Hsat.
  rewrite Mcnf.equisat_nnf in Hsat.
  eapply solve_mcnf_sound.
  - exact Hunsat.
  - exact Hsat.
Qed.


Corollary solve_mcnf_sound_contrapos : forall mc0,
  Mcnf.satisfiable mc0 ->
  Spec.Solution.is_sat (Spec.solve_mcnf mc0) = true.
Proof with try easy.
  intros mc0 Hsat. unfold Spec.Solution.is_sat.
  destruct (Spec.solve_mcnf mc0) eqn:Hunsat...
  exfalso. apply (solve_mcnf_sound mc0)...
  now rewrite Hunsat.
Qed.


Corollary solve_fml_sound_contrapos : forall phi,
  Fml.satisfiable phi ->
  Spec.Solution.is_sat (Spec.solve_fml phi) = true.
Proof with try easy.
  intros phi. unfold Spec.solve_fml, "|>".
  rewrite Nnf.equisat_fml, Mcnf.equisat_nnf.
  apply solve_mcnf_sound_contrapos.
Qed.
