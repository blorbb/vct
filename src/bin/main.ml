let parse_file path =
  let file_text = open_in path in
  let lexbuf = Lexing.from_channel file_text in
  Vct.Parser.file Vct.Lexer.next_token lexbuf
;;

let check fml =
  let result = Vct.Solver.NoModel.solve_fml fml in
  match Vct.Solver.NoModel.Solution.is_sat result with
  | true -> print_endline "SAT"
  | false -> print_endline "UNSAT"
;;

(* TODO: print out the model *)
let check_with_model fml =
  let result = Vct.Solver.TailRec.solve_fml fml in
  match Vct.Solver.TailRec.Solution.is_sat result with
  | true -> print_endline "SAT"
  | false -> print_endline "UNSAT"
;;

let () =
  match Sys.argv with
  | [| _; "--model"; f |] -> check_with_model (parse_file f)
  | [| _; f |] -> check (parse_file f)
  | _ ->
    Printf.eprintf "Usage: %s [--model] <input_file>\n" Sys.argv.(0);
    exit 1
;;
