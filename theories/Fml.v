From CegarTableaux Require Kripke Lit.


(** An arbitrary modal formula [Fml.t]. *)
Inductive t : Type :=
  | Var  (p : Atom.t)
  | Neg  (A : t)
  | And  (A B : t)
  | Or   (A B : t)
  | Impl (A B : t)
  | Box  (A : t)
  | Dia  (A : t).


Fixpoint force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  match phi with
  | Var  p   => Kripke.valuation M w0 p
  | Neg  A   => ~ force M w0 A
  | And  A B => force M w0 A /\ force M w0 B
  | Or   A B => force M w0 A \/ force M w0 B
  | Impl A B => force M w0 A -> force M w0 B
  | Box  A   => forall w1, R w0 w1 -> force M w1 A
  | Dia  A   => exists w1, R w0 w1 /\ force M w1 A
  end.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.

Definition unsatisfiable (phi : t) : Prop :=
  ~ satisfiable phi.


Definition satisfiable_kt (phi : t) : Prop :=
  exists W R (M : @Kripke.Kt.t W R) (w0 : W), force (Kripke.Kt.to_k M) w0 phi.

Definition unsatisfiable_kt (phi : t) : Prop :=
  ~ satisfiable_kt phi.
