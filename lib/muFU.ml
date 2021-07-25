open Core
   
module Syntax      = Hflmc2_syntax
module Options     = Hflmc2_options
(* module Util        = Hflmc2_util *)
module MuFU        = MuFU_core

let parse_to_raw_hes file =
  In_channel.with_file file ~f:begin fun ch ->
    let lexbuf = Lexing.from_channel ch in
    lexbuf.lex_start_p <- { lexbuf.lex_start_p with pos_fname = file };
    lexbuf.lex_curr_p  <- { lexbuf.lex_curr_p  with pos_fname = file };
    lexbuf
    |> Syntax.Parser.main
    end
;;

let parse_to_typed_hes file =
  let psi, _ = Syntax.parse_file file in
  psi

let print_output file txt =
  let fout = Out_channel.create (file ^ ".out") in
  Printf.fprintf fout "%s\n" txt;
  Out_channel.close fout
;;

let main file =
  let (psi, env)  = parse_to_raw_hes file in
  let psi' = MuFU.transform psi env in
  print_output file psi';
  ()
