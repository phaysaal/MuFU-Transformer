open Hflmc2_util
module Arith    = Arith
module Fixpoint = Fixpoint
module Print    = Print
module Formula  = Formula
module Hfl      = Hfl
module Hflz     = Hflz
module Id       = Id
module Type     = Type
module Raw_hflz = Raw_hflz
module IdMap    = IdMap
module IdSet    = IdSet
module Trans    = Trans

exception LexingError of string
exception ParseError of string
module Parser : sig
  val main : Lexing.lexbuf -> Raw_hflz.hes * (string * Type.abstraction_ty) list
end = struct
  module P = Parser
  module I = P.MenhirInterpreter

  let show_curr_pos lexbuf =
    let pos = Lexing.(lexbuf.lex_curr_p) in
    Fmt.strf "%s%d:%d"
      (if pos.pos_fname="" then "" else pos.pos_fname^":")
      pos.pos_lnum
      (pos.pos_cnum - pos.pos_bol)

  (*********************)
  (* Print error state *)
  (*********************)
  module type PRINTER_DEF = sig
    val print: string -> unit
    val print_symbol: I.xsymbol -> unit
    val print_element: (I.element -> unit) option
  end

  let make_printer ppf =
  (* {{{
   * 自動化する方法はあるにはあるけどmenhirレポジトリをcloneして
   * menhir-generate-printersというのをbuildする必要があって大変なので
   * やりたくない．悲しい *)
    let module User = struct
      let print s = Fmt.pf ppf "%s" s
      let print_symbol = function
        | I.X (I.T x) -> print @@ begin match x with
            | I.T_error     -> "error"
            | I.T_UIDENT    -> "UIDENT"
            | I.T_TRUE      -> "TRUE"
            | I.T_START_HES -> "START_HES"
            | I.T_STAR      -> "STAR"
            | I.T_RSQUARE   -> "RSQUARE"
            | I.T_RPAREN    -> "RPAREN"
            | I.T_RANGRE    -> "RANGRE"
            | I.T_PLUS      -> "PLUS"
            | I.T_OR        -> "OR"
            | I.T_NEQ       -> "NEQ"
            | I.T_NEG       -> "NEG"
            | I.T_MINUS     -> "MINUS"
            | I.T_LSQUARE   -> "LSQUARE"
            | I.T_LPAREN    -> "LPAREN"
            | I.T_LIDENT    -> "LIDENT"
            | I.T_LE        -> "LE"
            | I.T_LANGRE    -> "LANGRE"
            | I.T_LAMBDA    -> "LAMBDA"
            | I.T_INT       -> "INT"
            | I.T_GE        -> "GE"
            | I.T_FALSE     -> "FALSE"
            | I.T_EQ        -> "EQ"
            | I.T_EOF       -> "EOF"
            | I.T_DOT       -> "DOT"
            | I.T_COLON     -> "COLON"
            | I.T_DEF_L     -> "DEF_L"
            | I.T_DEF_G     -> "DEF_G"
            | I.T_AND       -> "AND"
            | I.T_TINT      -> "TINT"
            | I.T_TBOOL     -> "TBOOL"
            | I.T_TARROW    -> "TARROW"
            | I.T_START_ENV -> "START_ENV"
            | I.T_SEMICOLON -> "SEMICOLON"
            | I.T_FORALL    -> "FORALL"
            | I.T_SLASH     -> "SLASH"
            | I.T_PERCENT   -> "PERCENT"
            end
        | I.X (I.N x) -> print @@ begin match x with
            | I.N_uvar                     -> "uvar"
            | I.N_pred_expr                -> "pred_expr"
            | I.N_pred                     -> "pred"
            | I.N_nonempty_list_hflz_rule_ -> "nonempty_list_hflz_rule_"
            | I.N_lvar                     -> "lvar"
            | I.N_list_lvar_               -> "list_lvar_"
            | I.N_list_lambda_             -> "list_lambda_"
            | I.N_list_atom_               -> "list_atom_"
            | I.N_lambda                   -> "lambda"
            | I.N_lambdas                   -> "lambdas"
            | I.N_hflz_rule                -> "hflz_rule"
            | I.N_hflz                     -> "hflz"
            | I.N_hes                      -> "hes"
            | I.N_def_fixpoint             -> "def_fixpoint"
            | I.N_bool                     -> "bool"
            | I.N_atom                     -> "atom"
            | I.N_arith_expr               -> "arith_expr"
            | I.N_app_expr                 -> "app_expr"
            | I.N_and_or_expr              -> "and_or_expr"
            | I.N_abs_expr                 -> "abs_expr"
            | I.N_main                     -> "main"
            | I.N_env                      -> "env"
            | I.N_assignment               -> "assignment"
            | I.N_abstraction_ty           -> "abstraction_ty"
            | I.N_list_assignment_         -> "list_assignment_"
            | I.N_arith                    -> "arith"
            | I.N_and_or_predicate         -> "and_or_predicate"
            | I.N_abstraction_argty        -> "abstraction_argty"
            | I.N_a_predicate              -> "a_predicate"
            | I.N_predicate                -> "predicate"
            | I.N_atom_predicate           -> "atom_predicate"
            | I.N_atom_arith               -> "atom_arith"
            | I.N_loption_separated_nonempty_list_SEMICOLON_predicate__
                                           -> "loption_separated_nonempty_list_SEMICOLON_predicate__"
            | I.N_separated_nonempty_list_SEMICOLON_predicate_
                                           -> "separated_nonempty_list_SEMICOLON_predicate_"
            end
      let print_element = None
    end in (module User : PRINTER_DEF)
  (* }}} *)

  let pp_env ppf env =
    Fmt.pf ppf "%a"
      begin fun ppf env ->
        let module Printer =
          MenhirLib.Printers.Make(I)(val make_printer ppf)
        in
        Printer.print_env env
      end env


  (******************)
  (* Main procedure *)
  (******************)

  let loop lexbuf checkpoint =
    let succeed v = v in
    let fail checkpoint =
      match checkpoint with
      | I.HandlingError env ->
          raise @@ ParseError begin
            Fmt.strf "@[<v>Parse Error at %s:@;Cousumed input:@;%a@]@."
              (show_curr_pos lexbuf)
              pp_env env
          end
      | _ -> assert false
    in
    let supplier = I.lexer_lexbuf_to_supplier Lexer.token lexbuf in
    I.loop_handle succeed fail supplier checkpoint

  let main lexbuf =
    let hes, menv =
      try
        loop lexbuf (P.Incremental.main lexbuf.lex_curr_p)
      with Failure s ->
        raise @@ LexingError begin
          Print.strf "@[<v>Lexing Error at %s:@;%s@]@."
            (show_curr_pos lexbuf) s
        end
    in
    let env = match menv with None -> [] | Some env -> env in
    let item ppf (x,ty) =
      Print.pf ppf "@[<h>%s : %a@]" x Print.abstraction_ty ty
    in
    if false then Print.pr "@[<v>%a@]@."
      Print.(list item) env ;
    hes, env
end

let parse_string str =
  str
  |> Lexing.from_string
  |> Parser.main
  |> Raw_hflz.to_typed

let parse_file file =
  In_channel.with_file file ~f:begin fun ch ->
    let lexbuf = Lexing.from_channel ch in
    lexbuf.lex_start_p <- { lexbuf.lex_start_p with pos_fname = file };
    lexbuf.lex_curr_p  <- { lexbuf.lex_curr_p  with pos_fname = file };
    lexbuf
    |> Parser.main
    |> Raw_hflz.to_typed
  end

