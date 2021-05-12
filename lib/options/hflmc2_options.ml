
open Hflmc2_util

(******************************************************************************)
(* Options                                                                    *)
(******************************************************************************)

let oneshot = ref false

module Preprocess = struct
  let inlining = ref (Obj.magic())
end

module Abstraction = struct
  (* NOTE Actual value is set by Cmdliner *)
  let max_I                = ref (Obj.magic())
  let max_ands             = ref (Obj.magic())
  let modify_pred_by_guard = ref (Obj.magic())
end

module Refine = struct
  (* NOTE Actual value is set by Cmdliner *)
  let use_legacy           = ref (Obj.magic())
end

module Typing = struct
  let solver               = ref (Obj.magic())
  let show_refinement      = ref (Obj.magic())
  let mode_burn_et_al      = ref (Obj.magic())
  let no_disprove          = ref (Obj.magic())
end

(******************************************************************************)
(* Util(?)                                                                    *)
(******************************************************************************)

let set_ref ref x = ref := x
let set_ref_opt ref x = match x with None -> () | Some x -> ref := x
let set_module_log_level level modules =
  let logs = Logs.Src.list() in
  List.iter logs ~f:begin fun src ->
    if List.mem modules (Logs.Src.name src) ~equal:String.equal
    then begin
      Logs.Src.set_level src (Some level)
    end
  end

(******************************************************************************)
(* Parser                                                                     *)
(******************************************************************************)

type params =
  { input : string list [@pos 0] [@docv "FILE"]

  (* Whole procedure *)
  ; oneshot : bool [@default false]
    (** Stop execution after first CEGAR loop *)

  (* Preprocess *)
  ; no_inlining : bool [@default false]
    (** Disable inlining *)

  (* Logging *)
  ; log_debug : string list [@default []] [@docs "Log"] [@docv "MODULE,..."] [@aka ["debug"]]
    (** Enable debug log of modules *)
  ; log_info  : string list [@default []] [@docs "Log"] [@docv "MODULE,..."]
    (** Enable info log of modules *)

  (* Abstraction *)
  ; abst_max_I : int [@default 2] [@docs "Abstraction"]
    (** Maximum number of conjunction in the assumption of predicate abstraction *)

  ; abst_max_ands : int [@default 10] [@docs "Abstraction"]
    (** Maximum number of conjunction in predicate abstraction *)

  ; abst_no_modify_pred_by_guard : bool [@default false] [@docs "Abstraction"]
    (** Do not modify [pred] into [C => pred] *)

  (* Refine *)
  ; refine_legacy : bool [@default false] [@docs "Refine"]
    (** Use old refine algorithm *)
  
  (* Typing *)
  ; solver : string [@default "auto"] [@docs "Typing"] [@docv "solver_name"]
  (** Choose background CHC solver. Available: auto z3, hoice, fptprover *)

  ; show_refinement: bool [@default false] [@docs "Typing"] [@docv "show refinement"]
  (** Show refinement types. This sometimes fails because of parsing the solution from CHC solver... *)

  ; mode_burn_et_al: bool [@default false] [@docs "Typing"] [@docv "Use the subtyping rule of burn et al"]
  (** Use Subtying rule in burn et al *)

  ; no_disprove: bool [@default false]
    (** Disable disproving*)
  }
  [@@deriving cmdliner,show]

let set_up_params params =
  set_module_log_level Debug               params.log_debug;
  set_module_log_level Info                params.log_info;
  set_ref oneshot                          params.oneshot;
  set_ref Preprocess.inlining              (not params.no_inlining);
  set_ref Abstraction.max_I                params.abst_max_I;
  set_ref Abstraction.max_ands             params.abst_max_ands;
  set_ref Abstraction.modify_pred_by_guard (not params.abst_no_modify_pred_by_guard);
  set_ref Refine.use_legacy                params.refine_legacy;
  set_ref Typing.solver                    params.solver;
  set_ref Typing.show_refinement           params.show_refinement;
  set_ref Typing.mode_burn_et_al           params.mode_burn_et_al;
  set_ref Typing.no_disprove               params.no_disprove;
  params.input

(******************************************************************************)
(* Term                                                                       *)
(******************************************************************************)

let term_set_up_params () =
  Cmdliner.Term.(const set_up_params $ params_cmdliner_term ())

(* Log *)
let term_setup_log () =
  (*{{{*)
  let setup style_renderer level =
    Format.set_margin 100;
    Fmt_tty.setup_std_outputs ?style_renderer ();
    let pp_header ppf (src, level, header) =
      let src_str =
        if Logs.Src.(equal src Logs.default)
        then None
        else Some (Logs.Src.name src)
      in
      let level_str, style = match (level : Logs.level) with
        | App     -> "App"     , Logs_fmt.app_style
        | Error   -> "Error"   , Logs_fmt.err_style
        | Warning -> "Warning" , Logs_fmt.warn_style
        | Info    -> "Info"    , Logs_fmt.info_style
        | Debug   -> "Debug"   , Logs_fmt.debug_style
      in
      let (<+) x y = match x with None -> y | Some x -> x ^ ":" ^ y in
      let (+>) x y = match y with None -> x | Some y -> x ^ ":" ^ y in
      let str = src_str <+ level_str +> header in
      Fmt.pf ppf "@[<v 2>[%a]@ @]" Fmt.(styled style string) str
    in
    let reporter =
      { Logs.report = fun src level ~over k msgf ->
          let k _ = over (); k () in
          msgf @@ fun ?header ?tags:_ fmt ->
            let ppf = Fmt.stdout in
            Format.kfprintf k ppf ("%a@[" ^^ fmt ^^ "@]@.")
              pp_header (src, level, header)
      }
    in
    Logs.set_reporter reporter;
    Logs.set_level level
  in
    Cmdliner.Term.(const setup $ Fmt_cli.style_renderer () $ Logs_cli.level ())
(*}}}*)

type input = [`File of string | `Stdin]
let parse ?argv () : input option =
  let term () =
    let open Cmdliner.Term in
    const (fun _ file -> file)
      $ term_setup_log () (* NOTE order matters *)
      $ term_set_up_params ()
  in match Cmdliner.Term.(eval ?argv (term (), info "hflmc2")) with
  | `Ok [] -> Some `Stdin
  | `Ok [file] -> Some (`File file)
  | `Ok _ -> Fn.todo ~info:"multiple input files" ()
  | _     -> None

