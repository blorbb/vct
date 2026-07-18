From Stdlib Require Extraction ExtrOcamlBasic.
From CegarTableaux Require Mcnf Tree Solver CplSolver.

Extraction Language OCaml.
Set Extraction Output Directory "src/lib/gen".
Extraction Blacklist Bindings Lexer Parser.

(** The axioms depend on a module named [Bindings] being accessible with
    the correct implementation. *)
Extract Constant CplSolver.t => "Bindings.t".
Extract Constant CplSolver.make => "Bindings.make".
Extract Constant CplSolver.add_clause => "Bindings.add_clause".
Extract Constant CplSolver.solve_with_assumptions => "Bindings.solve_with_assumptions".

(** Extract [Atom.t] to OCaml [int].

    This is adapted from [ExtrOcamlZInt]. *)

Extract Inductive Atom.t => "int"
  (* Construct int from positive *)
  [ "(let rec int_of_pos = function
        | Coq_xH -> 1
        | Coq_xO p -> 2 * int_of_pos p
        | Coq_xI p -> 2 * int_of_pos p + 1
      in int_of_pos)"
  ]
  (* Construct positive from int. *)
  "(fun f n ->
      let rec pos_of_int x =
        if x <= 1 then Coq_xH
        else if x mod 2 = 0 then Coq_xO (pos_of_int (x / 2))
        else Coq_xI (pos_of_int (x / 2))
      in f (pos_of_int n))".

Extract Constant Atom.one => "1".
Extract Constant Atom.succ => "Stdlib.Int.succ".
Extract Constant Atom.max => "Stdlib.Int.max".
Extract Constant Atom.ltb => "(<)".
Extract Constant Atom.leb => "(<=)".
Extract Constant Atom.eqb => "Stdlib.Int.equal".
Extract Constant Atom.eq_dec => "Stdlib.Int.equal".
Extract Constant Atom.compare =>
  "fun x y -> if x=y then Eq else if x<y then Lt else Gt".


Separate Extraction
  Solver.Spec.solve_fml
  Solver.Spec.Solution.is_sat
  Solver.TailRec.solve_fml
  Solver.TailRec.Solution.is_sat
  Solver.NoModel.solve_fml
  Solver.NoModel.Solution.is_sat
  Solver.Cached.solve_fml
  Solver.Cached.Solution.is_sat
  Solver.FiredBoxes.solve_fml
  Solver.FiredBoxes.Solution.is_sat.
