open Core
   
module Syntax      = MuFU_syntax
module Options     = MuFU_options
(* module Util        = Hflmc2_util *)
module MuFU        = MuFU_core

let parse_to_raw_hes file =
  In_channel.with_file file ~f:begin fun ch ->
    let lexbuf = Lexing.from_channel ch in
    lexbuf.lex_start_p <- { lexbuf.lex_start_p with pos_fname = file };
    lexbuf.lex_curr_p  <- { lexbuf.lex_curr_p  with pos_fname = file };
    lexbuf
    |> Syntax.Parser.main
    |> fst
    end
;;

let parse_to_typed_hes file =
  let psi, _ = Syntax.parse_file file in
  psi
                   
let main file =
  let psi  = parse_to_raw_hes file in
  let psi' = MuFU.transform psi in
  print_string (string_of_int (List.length psi'));
  ()