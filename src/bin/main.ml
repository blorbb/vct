let check fml =
  let result = Vct.Solver.solve_fml fml in
  match result with
  | Vct.Search.Solution.Sat _ -> print_endline "SAT"
  | Vct.Search.Solution.Unsat (_, _) -> print_endline "UNSAT"
;;

let check_file filename =
  let file_text = open_in filename in
  let lexbuf = Lexing.from_channel file_text in
  let fml = Vct.Parser.file Vct.Lexer.next_token lexbuf in
  check fml
;;

let () =
  match Array.length Sys.argv with
  | 2 -> check_file Sys.argv.(1)
  | _ ->
    Printf.eprintf "Usage: %s <input_file>\n" Sys.argv.(0);
    exit 1
;;
