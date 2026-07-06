From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From CegarTableaux Require Mcnf Tree Solver CplSolver.

Extraction Language OCaml.
Set Extraction Output Directory "src/lib".
Extraction Blacklist bindings.

(** The axioms depend on a module named [Bindings] being accessible with
    the correct implementation. *)
Extract Constant CplSolver.t => "Bindings.t".
Extract Constant CplSolver.make => "Bindings.make".
Extract Constant CplSolver.add_clause => "Bindings.add_clause".
Extract Constant CplSolver.solve_with_assumptions => "Bindings.solve_with_assumptions".


(** [Lit.atm] is needed in the OCaml bindings but is not used by [solve_fml]. *)
Separate Extraction Solver.Spec.solve_fml Solver.TailRec.solve_fml Solver.NoModel.solve_fml Solver.Cached.solve_fml Lit.atm.
