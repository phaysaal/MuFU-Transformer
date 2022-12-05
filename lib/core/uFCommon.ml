open Hflmc2_syntax
   
module H = Raw_hflz
module F = Formula
module A = Arith
module L = Tools
module P = Printer
module Z = Z3Interface
module U = MatchMaker
         
module D = Map.Make(String)
module AP = ArithmeticProcessor

type hfl = H.raw_hflz

exception StrangeSituation of string

let newpredcount = ref 0;;

let new_predicate_name () =
  newpredcount := !newpredcount + 1;
  "FIXPRED" ^ string_of_int !newpredcount;;
                            
let rec mk_ors = function
    [] -> H.Pred (Formula.Eq, [H.Int 0; Int 1])
  | [f] -> f
  | f::fs ->
     H.Or (f, mk_ors fs)
;;
  
let rec mk_ands = function
    [] -> H.Pred (Formula.Eq, [H.Int 0; Int 0])
  | [f] -> f
  | f::fs ->
     H.And (f, mk_ands fs)
;;

let rec cnf_of_formula f =
  let rec mk_left x y =
    match y with
    | H.And (a, b) -> H.mk_and (mk_left x a) (mk_left x b)
    | _ -> H.mk_or x y |> dnf_of_formula
  in
  let rec mk_right x y = match x with
    | H.And (a, b) -> H.mk_and (mk_right a y) (mk_right b y)
    | _ -> mk_left x y
  in
  let rec mk f =
    match f with
    | H.And (f1, f2) -> H.mk_and (mk f1) (mk f2)
    | H.Or (f1, f2) -> mk_right (mk f1) (mk f2)
    | _ -> f 
  in
  let f' = mk f |> U.get_conjuncts |> mk_ands in
  f'

and dnf_of_formula f =
  let rec mk_left x y =
    match y with
    | H.Or (a, b) -> H.mk_or (mk_left x a) (mk_left x b)
    | _ -> H.mk_and x y |> cnf_of_formula
  in
  let rec mk_right x y = match x with
    | H.Or (a, b) -> H.mk_or (mk_right a y) (mk_right b y)
    | _ -> mk_left x y
  in
  let rec mk f =
    match f with
    | H.Or (f1, f2) -> H.mk_or (mk f1) (mk f2)
    | H.And (f1, f2) -> mk_right (mk f1) (mk f2)
    | _ -> f 
  in
  let f' = mk f |> U.get_disjuncts |> mk_ors in
  f'
;;

let rec subtract s = function
    [] -> []
  | s'::xs when s'=s -> subtract s xs
  | x ::xs -> x::subtract s xs;;

let rec fv f =
  match f with
  | H.Bool _ -> []
  | H.Var s -> [s]
  | H.Or (f1, f2) ->
     fv f1 @ fv f2
  | H.And (f1, f2) ->
     fv f1 @ fv f2
  | H.Abs (s, f1) ->
     fv f1 |> (subtract s)
  | H.App (H.Var _, f2) ->
     fv f2
  | H.App (f1, f2) ->
     fv f1 @ fv f2
  | H.Int _ -> []
  | H.Op (_, f1) ->
     List.map fv f1 |> List.concat
  | H.Pred (_, f1) ->
     List.map fv f1 |> List.concat
  | H.Exists (s, f1) ->
     fv f1 |> (subtract s)
  | H.Forall (s, f1) ->
     fv f1 |> (subtract s)
;;

let subs_vars params args f =
  let p_t =
    try
      List.combine params args
    with
      _ ->
      raise ( StrangeSituation "Param-Args mismatch")
  in
  List.fold_left (fun f (to_be, by) ->
      U.subs_var to_be by f
    ) f p_t
;;

(** n -> ["..$n"; "..$(n-1)"; ...; "..1"] *)
let rec get_temps_n n =
  if n > 0 then
    (".." ^ (string_of_int n)) ::get_temps_n (n-1)
  else
    []
;;

let exec_unfold defs_map f =
  let res : (string * hfl list) = try U.explode_pred f with e -> print_endline "exec_unfold"; raise e in
  let f (pred_name, args) =
    let pred = try
        D.find pred_name defs_map
      with e ->
        print_int (D.cardinal defs_map); 
        print_endline pred_name; raise e in
    let params : string list = pred.H.args in
    let temps = get_temps_n (List.length args) in (** [t1; t2; ...] = ["..$n"; "..$(n-1)"; ...; "..1"] *)
    let vtemps = List.map (fun t -> H.Var t) temps in
  
    let body' = subs_vars params vtemps pred.H.body in (** body[x1:=t1; ...] *)
    let body'' = subs_vars temps args body' in (** body[x1:=arg1; ...] *)
    body''
  in
  f res
;;

let fold goal body =
  P.pp_formula body |> P.dbgn "Before Fold";
  let res, body' = U.find_matching goal.H.fix goal.H.var goal.H.args goal.H.body body in
  if res then P.pp_formula body' |> P.dbgn "After Fold";
  res, body'
;;

let add_map map def =
  D.add def.H.var def map
;;

let make_def_map defs =
  List.fold_left add_map D.empty defs 
;;


let mk_rule n a f b =
  {
    H.var = n;
    args = a;
    fix = f;
    body = b
  }
;;

let rec exist_free = function H.Exists (_, f) -> exist_free f | f -> f 
let is_pred = function H.App _ -> true | _ -> false
;;


let substitute_args to_be by (args : hfl list) =
  if List.length to_be <> List.length by then
    raise (StrangeSituation "tobe <> by in substitution")
  else
    let temps = get_temps_n (List.length to_be) in
    let subs_pair1 = try List.combine to_be (List.map H.mk_var temps) with e -> print_endline "substitute args"; raise e in
    let subs_pair2 = List.combine temps by in
    let subs_arg (arg:hfl) ((to_be:string), (by:hfl)) : hfl = U.subs_var to_be by arg |> AP.normalize in
    List.map (fun arg ->
        let arg' = List.fold_left subs_arg arg subs_pair1 in
        List.fold_left subs_arg arg' subs_pair2
      ) args
;;
