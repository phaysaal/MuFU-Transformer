open Hflmc2_syntax
   
module H = Raw_hflz
module F = Formula
module A = Arith

module P = Printer
module Z = Z3Interface
module U = MatchMaker
         
module D = Map.Make(String)
module AP = ArithmeticProcessor

type hfl = H.raw_hflz

exception StrangeSituation of string
exception UnsupportedNow of string

exception Err
exception NotFoldable

let var_seq = ["x"; "y"; "z"; "w"; "r"; "p"; "q"; "m"; "n"];;

let new_params n =
  let l = List.length var_seq in
  let rec aux = function
      i when i = n -> []
    | i ->
       if i < l then
         List.nth var_seq i::aux (i+1)
       else
         ("p" ^ (string_of_int (l-i)))::aux (i+1)
  in
  aux 0
;;
                          
let newpredcount = ref 0;;

let new_predicate_name () =
  newpredcount := !newpredcount + 1;
  "FIXPRED" ^ string_of_int !newpredcount;;
                       
let equiv f1 f2 =
  f1 = f2;;

let is_taut f =
  Z.is_tautology f
;;

let is_unsat f =
  let r = 
    if f = H.Bool false then
      true
    else
      Z.is_unsat f
  in
  r
;;

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

let rec get_pred_name = function
    H.Var s -> s
  | H.App (f, _) -> get_pred_name f
  | _ -> raise (StrangeSituation "Not a predicate")
;;

let get_pred defs_map f =
  let pred_name = get_pred_name f in
  let pred = try D.find pred_name defs_map with Not_found -> print_endline ("Not found predicate " ^ pred_name); raise Not_found in
  pred;;

let not_taut_exists s f =
  let t = H.Exists (s, f) in
  not (is_taut t)
;;

let rec is_in x f =
  let f' =
  match f with
  | H.Bool _ -> false
  | H.Var s when s=x -> true
  | H.Var _ -> false
  | H.Or (f1, f2) ->
     is_in x f1 || is_in x f2
  | H.And (f1, f2) ->
     is_in x f1 || is_in x f2
  | H.Abs (s, f1) ->
     if s=x then false else is_in x f1
  | H.App (f1, f2) ->
     is_in x f1 || is_in x f2
  | H.Int _ -> false
  | H.Op (_, f1) ->
     List.exists (fun f -> is_in x f) f1
  | H.Pred (_, f1) ->
     List.exists (fun f -> is_in x f) f1
  | H.Exists (s, f1) ->
     if s=x then false else is_in x f1
  | H.Forall (s, f1) ->
     if s=x then false else is_in x f1
  in
  f'
;;

let compare_raw_hflz f1 f2 =
  match f1, f2 with
  | H.Pred _, H.App _ ->
     -1
  | H.App _, H.Pred _ ->
     1
  | _ ->
     H.compare_raw_hflz f1 f2
;;

let mk fn (f1, f2) =
  if compare_raw_hflz f1 f2 <= 0 then
    fn f1 f2
  else
    fn f2 f1
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
  let f' = mk f |> U.get_conjuncts |> (* List.sort compare_raw_hflz |> *) mk_ands in
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
  let f' = mk f |> U.get_disjuncts |> (* List.sort compare_raw_hflz |> *) mk_ors in
  f'
;;

let build_exists s f =
  if is_in s f then
    H.Exists (s, f)
  else
    f
;;

let ex_dist f =
  let rec ex_dist f =
  match f with
  | H.Bool _ -> f
  | H.Var _ -> f
  | H.Or (f1, f2) ->
     H.Or (ex_dist f1, ex_dist f2)
  | H.And (f1, f2) ->
     H.And (ex_dist f1, ex_dist f2)
  | H.Abs (s, f1) ->
     H.Abs (s, ex_dist f1)
  | H.App (f1, f2) ->
     H.App (ex_dist f1, ex_dist f2)
  | H.Int _ -> f
  | H.Op (o, f1) ->
     H.Op (o, List.map ex_dist f1)
  | H.Pred (p, f1) ->
     H.Pred (p, List.map ex_dist f1)
  | H.Exists (s, H.Or (f1, f2)) ->
     let f' = H.Or (build_exists s f1, build_exists s f2) in
     ex_dist f'
  | H.Exists (s, H.And (f1, f2)) ->
     begin
       let b1 = is_in s f1 in
       let b2 = is_in s f2 in
       if b1 && b2 then
          H.Exists (s, ex_dist (H.And(f1, f2)))
       else if b1 then
          ex_dist (H.And (H.Exists (s, f1), f2))
       else if b2 then
          ex_dist (H.And (f1, H.Exists (s, f2)))
       else
          ex_dist (H.And (f1, f2))
     end
  | H.Exists (s, f1) ->
     build_exists s (ex_dist f1)
  | H.Forall (s, f1) ->
     H.Forall (s, ex_dist f1)
  in
  let f' = ex_dist f in
  P.pp_formula f' |> P.dbg "EX dist";
  f'
;;


let taut_elim f =
  let rec taut_elim f =
  match f with
  | H.Bool _ -> f
  | H.Var _ -> f
  | H.Or (f1, f2) ->
     if is_taut f1 || is_taut f2 then
       H.mk_bool true
     else
       H.Or (taut_elim f1, taut_elim f2)
  | H.And (f1, f2) ->
     let f1' = taut_elim f1 in
     let f2' = taut_elim f2 in
     let b1 = is_taut f1' in
     let b2 = is_taut f2' in
     if b1 && b2 then
       H.Bool true
     else if b1 then
       f2'
     else if b2 then
       f1'
     else
       H.And (f1', f2')
  | H.Abs (_, _) ->
     f
  | H.App (_, _) ->
     f
  | H.Int _ -> f
  | H.Op (_, _) ->
     f
  | H.Pred (_, _) ->
     f
  | H.Exists (s, f1) ->
     let f1' = taut_elim f1 in
     if is_taut f1' then
       H.mk_bool true
     else
       H.Exists (s, f1')
  | H.Forall (s, f1) ->
     let f1' = taut_elim f1 in
     if is_taut f1' then
       H.mk_bool true
     else
       H.Exists (s, f1')
  in
  let f' = taut_elim f in
  P.pp_formula f' |> P.dbg "tautology elimination";
  f'
;;

let unsat_elim f =
  let rec unsat_elim = function
      H.And (f1, f2) ->
       if is_unsat f1 || is_unsat f2 then
         H.Bool false
       else
         H.And (unsat_elim f1, unsat_elim f2)
    | H.Or (f1, f2) ->
       let b1 = is_unsat f1 in
       let b2 = is_unsat f2 in
       if b1 && b2 then
         H.Bool false
       else if b1 then
         unsat_elim f2
       else if b2 then
         unsat_elim f1
       else
         H.Or (unsat_elim f1, unsat_elim f2)
    | H.Exists (s, f1) ->
       let f1' = unsat_elim f1 in
       if f1' = H.Bool false then
         f1'
       else
         H.Exists (s, f1')
    | H.Forall (s, f1) ->
       let f1' = unsat_elim f1 in
       if f1' = H.Bool false then
         f1'
       else
         H.Forall (s, f1')
    | f -> if is_unsat f then H.Bool false else f
  in
  let f' = unsat_elim f in
  P.pp_formula f' |> P.dbg "unsat elimination";
  f'
;;

let normalize f =
  f
  |> ex_dist
  |> cnf_of_formula
  |> taut_elim
;;

(** n -> ["..$n"; "..$(n-1)"; ...; "..1"] *)
let rec get_temps_n n =
  if n > 0 then
    (".." ^ (string_of_int n)) ::get_temps_n (n-1)
  else
    []
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

(* let exec_unfold_ext defs_map f =
  let res : (string * hfl list) = try explode_pred f with e -> print_endline "exec_unfold"; raise e in
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
    (pred_name, args, body'', f)
  in
  f res
;; *)

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

(* let exec_unfold defs_map f =
  let (_, _, body, _) = exec_unfold_ext defs_map f in
  body
;; *)

let unfold_formula defs_map f =
  let rec unfold_formula defs_map f =
    match f with
    | H.Bool _ -> f
    | H.Var _ -> f
    | H.Or (f1, f2) ->
       H.mk_or (unfold_formula defs_map f1) (unfold_formula defs_map f2)
    | H.And (f1, f2) ->
       H.mk_and (unfold_formula defs_map f1) (unfold_formula defs_map f2)
    | H.Abs (s, f1) ->
       H.mk_abs s (unfold_formula defs_map f1)
    | H.App (_, _) ->
       exec_unfold defs_map f
    | H.Int _ -> f
    | H.Op (o, f1) ->
       H.mk_op o (List.map (unfold_formula defs_map ) f1)
    | H.Pred (p, f1) ->
       H.Pred (p, List.map (unfold_formula defs_map ) f1)
    | H.Exists (s, f1) ->
       H.Exists (s, unfold_formula defs_map  f1)
    | H.Forall (s, f1) ->
       H.Forall (s, unfold_formula defs_map f1)
  in
  let f' = unfold_formula defs_map f in
  P.pp_formula f' |> P.dbg "Unfolded";
  f'
;;

let controlled_unfold_formula pred_set defs_map f =
  let rec unfold_formula defs_map f =
    match f with
    | H.Bool _ -> f
    | H.Var _ -> f
    | H.Or (f1, f2) ->
       H.mk_or (unfold_formula defs_map f1) (unfold_formula defs_map f2)
    | H.And (f1, f2) ->
       H.mk_and (unfold_formula defs_map f1) (unfold_formula defs_map f2)
    | H.Abs (s, f1) ->
       H.mk_abs s (unfold_formula defs_map f1)
    | H.App _ when List.mem f pred_set ->
       exec_unfold defs_map f
    | H.App _ -> f
    | H.Int _ -> f
    | H.Op (o, f1) ->
       H.mk_op o (List.map (unfold_formula defs_map ) f1)
    | H.Pred (p, f1) ->
       H.Pred (p, List.map (unfold_formula defs_map ) f1)
    | H.Exists (s, f1) ->
       H.Exists (s, unfold_formula defs_map  f1)
    | H.Forall (s, f1) ->
       H.Forall (s, unfold_formula defs_map f1)
  in
  let f' = unfold_formula defs_map f in
  P.pp_formula f' |> P.dbg "Unfolded";
  f'
;;

let unfold_one_pred pred_name defs_map f =
  let rec unfold_formula defs_map f =
    match f with
    | H.Bool _ -> f
    | H.Var _ -> f
    | H.Or (f1, f2) ->
       H.mk_or (unfold_formula defs_map f1) (unfold_formula defs_map f2)
    | H.And (f1, f2) ->
       H.mk_and (unfold_formula defs_map f1) (unfold_formula defs_map f2)
    | H.Abs (s, f1) ->
       H.mk_abs s (unfold_formula defs_map f1)
    | H.App _ when fst (U.explode_pred f) = pred_name ->
       exec_unfold defs_map f
    | H.App _ -> f
    | H.Int _ -> f
    | H.Op (o, f1) ->
       H.mk_op o (List.map (unfold_formula defs_map ) f1)
    | H.Pred (p, f1) ->
       H.Pred (p, List.map (unfold_formula defs_map ) f1)
    | H.Exists (s, f1) ->
       H.Exists (s, unfold_formula defs_map  f1)
    | H.Forall (s, f1) ->
       H.Forall (s, unfold_formula defs_map f1)
  in
  let f' = unfold_formula defs_map f in
  P.pp_formula f' |> P.dbg "Unfolded";
  f'
;;

let preds_eq pred1 pred2 =
  try
    let (p1, args1) = U.explode_pred pred1 in
    let (p2, args2) = U.explode_pred pred2 in
    p1 = p2 && List.for_all (fun (a,b) -> is_taut (H.Pred (Formula.Eq, [a;b]))) (List.combine args1 args2)
  with
    _ -> false
;;

let unfold_pred pred defs_map f =
  let rec unfold_formula defs_map f =
    match f with
    | H.Bool _ -> f
    | H.Var _ -> f
    | H.Or (f1, f2) ->
       H.mk_or (unfold_formula defs_map f1) (unfold_formula defs_map f2)
    | H.And (f1, f2) ->
       H.mk_and (unfold_formula defs_map f1) (unfold_formula defs_map f2)
    | H.Abs (s, f1) ->
       H.mk_abs s (unfold_formula defs_map f1)
    | H.App _ when preds_eq f pred ->
       exec_unfold defs_map f
    | H.App _ -> f
    | H.Int _ -> f
    | H.Op (o, f1) ->
       H.mk_op o (List.map (unfold_formula defs_map ) f1)
    | H.Pred (p, f1) ->
       H.Pred (p, List.map (unfold_formula defs_map ) f1)
    | H.Exists (s, f1) ->
       H.Exists (s, unfold_formula defs_map  f1)
    | H.Forall (s, f1) ->
       H.Forall (s, unfold_formula defs_map f1)
  in
  let f' = unfold_formula defs_map f in
  P.pp_formula f' |> P.dbg "Unfolded";
  f'
;;


let mk_rule n a f b =
  {
    H.var = n;
    args = a;
    fix = f;
    body = b
  }
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


let var_compare x y =
  match x, y with
    "x", _ when y<>"x" -> -1
  | "y", _ when y<>"y" -> -1
  | "z", _ when y<>"z" -> -1
  | _, "x" when y<>"x" -> 1
  | _, "y" when y<>"y" -> 1
  | _, "z" when y<>"z" -> 1
  | _, _ -> String.compare x y
;;

let uniq ls =
  let rec aux acc = function
      [] -> []
    | x::xs ->
       if List.mem x acc then
         aux acc xs
       else
         x::aux (x::acc) xs
  in 
  aux [] ls
;;

let make_new_goal f =
  let newpredname = new_predicate_name () in
  let fvs = U.fv f |> List.sort_uniq var_compare in
  let newpred = List.map H.mk_var fvs
                |> U.implode_pred newpredname
  in
  let newpreddef = mk_rule newpredname fvs Fixpoint.Greatest f in
  (Some newpreddef, newpred)
;;

let rec transform_goal = function
  | H.And _ as f-> make_new_goal f
  | H.Or (H.App _, _) as f ->
     make_new_goal f
  | H.Or (f1, f2) as f ->
     begin
       let (res, f2') = transform_goal f2 in
       match res with
         None -> (res, f)
       | Some _ -> (res, H.Or (f1, f2'))
     end
  | H.App _ as f ->
     make_new_goal f
  | f ->
     (None, f)
;;

let concat_option res1 res2 =
  match res1, res2 with
    Some nf1, Some nf2 -> Some (nf1@nf2) 
  | Some _, _ -> res1
  | _, _ -> res2
;;

let op_apply fn (a, b) =
  let (a', b') = fn b in
  (concat_option a a', b')
;;

let snd_apply fn (a, b) =
  let b' = fn b in
  (a, b')
;;

let is_candidate s args =
  List.exists (fun a -> let fvs = U.fv a in fvs = [s] || List.length fvs = 0) args
;;

let reduce_args qvs args =
  List.filter (fun (_, a) -> let fvs = U.fv a in List.for_all (fun sv -> fvs <> [sv]) qvs && List.length fvs > 0) args
;;

let reduce_args1 sv args =
  List.filter (fun  a -> let fvs = U.fv a in fvs <> [sv] && List.length fvs > 0) args
;;

let rec ex_trans_formula s predname newpredname = function
    H.Exists (s', ((H.App _) as f)) when s'=s ->
    let (p, args) = U.explode_pred f in
    if p = predname then
      let args' = reduce_args1 s args in
      U.implode_pred newpredname args'
    else
      H.Exists (s', f)
  | H.And (f1, f2) ->
     H.And (ex_trans_formula s predname newpredname f1, ex_trans_formula s predname newpredname f2)
  | H.Or (f1, f2) ->
     H.Or (ex_trans_formula s predname newpredname f1, ex_trans_formula s predname newpredname f2)    
  | f -> f;;

let reverse_subs p_a f =
  let (p,a) = List.split p_a in
  let p' = List.map H.mk_var p in
  let a_p = List.combine a p' in
  let f' = List.fold_left (fun f (to_be, by) ->
      U.subs_f to_be by f
             ) f a_p in
  P.pp_formula f' |> P.dbg "Reverse Substitution";
  f'
;;

let rec conj_to_list = function
    H.And (f1, f2) ->
    conj_to_list f1 @ conj_to_list f2
  | x -> [x]
;;

let rec list_to_and = function
    [] -> H.Bool true
  | [x] -> x
  | x::xs -> H.And (x, list_to_and xs)
;;

let get_value x f =
  match f with
    H.Pred (Formula.Eq, a::b::_) ->
     begin
       let (c1,d1) = AP.cx_d x a in
       let (c2,d2) = AP.cx_d x b in
       let r =
         match c1 with
           [] ->
            begin
              (** d1 = x*c2+d2 ==> x = (d1-d2)/c2  *)
              match c2 with
                (Arith.Sub, _)::_ ->
                 let c2' = AP.neg_list c2 in
                 H.Op (Arith.Div, [H.Op (Arith.Sub, [AP.list_to_exp d2; AP.list_to_exp d1]); AP.list_to_exp c2'])
              | _ ->
                 H.Op (Arith.Div, [H.Op (Arith.Sub, [AP.list_to_exp d1; AP.list_to_exp d2]); AP.list_to_exp c2])
            end
         | _ ->
            match c2 with
              [] ->
              (** x*c1+d1 = d2 ==> x = (d2-d1)/c1  *)
              H.Op (Arith.Div, [H.Op (Arith.Sub, [AP.list_to_exp d2; AP.list_to_exp d1]); AP.list_to_exp c1])
            | _ ->
               (** x*c1+d1 = x*c2+d2 ==> x = (d2-d1)/(c1-c2)  *)
               H.Op (Arith.Div, [H.Op (Arith.Sub, [AP.list_to_exp d2; AP.list_to_exp d1]); H.Op (Arith.Sub, [AP.list_to_exp c1; AP.list_to_exp c2])])
       in
       let r' = AP.normalize r in
       r'
       
     end
  | _ -> raise (UnsupportedNow "get_value")
;;

let combine_res = List.hd
;;

(** SINGLE CONSTRAINT *)
let rec find_constraint x f =
  let conjs = conj_to_list f in
  
  let constraints, nonconstraints = List.partition (function H.Pred (Formula.Eq, _) as c -> List.mem x (U.fv c) | _ -> false) conjs in
  match constraints with
    [] -> f, false
  | _ ->
     let constraints' = List.sort_uniq (fun a b ->
                            if List.length (U.fv a) - List.length (U.fv b) < 0 then -1 else 1) constraints in
     let the_constraint = List.hd constraints' in
     let value = get_value x the_constraint in
     let nonconstraints' = List.map (U.subs_var x value) ((List.tl constraints') @ nonconstraints) in
     list_to_and nonconstraints', List.length nonconstraints' <> List.length conjs
;;

let rec is_atomic = function
    H.Pred _ -> true
  | H.And _ -> false
  | H.Or _ -> false
  | H.App _ -> true
  | H.Exists _ -> true
  | _ -> true
;;

let predicate_for_exists goal =
  let newgoalname = new_predicate_name () in
  let args = List.map H.mk_var goal.H.args in
  let p_a = List.combine goal.H.args args in
  newgoalname, p_a, args, goal.H.fix
;;

let rec has_constraint = function
    H.Pred _ -> true
  | H.And (f1, f2) -> has_constraint f1 || has_constraint f2
  | H.Or (f1, f2) -> has_constraint f1 || has_constraint f2
  | _ -> false
;;

let get_qvs_and_body f =
  let rec aux qvs = function
      H.Exists (s, f) ->
      aux (s::qvs) f
    | f ->
       (qvs, f)
  in
  let (qvs, f') = aux [] f in
  (qvs, f')
;;

let rec unfold_fold ?(time=0) transformer goal defs_map f =
  let f' = unfold_formula defs_map f in
  let f'' = transformer f' in
  let is_matched, f' = fold goal f'' in
  if is_matched then
    begin
      let fv_f' = U.fv f' in
      let params = List.filter (fun v -> List.mem v fv_f') goal.H.args in

      let newpred = mk_rule goal.var params goal.fix f' in
      Some ([newpred], params)
    end
  else
    if time > 2 then
      None
    else
      begin
        print_endline "Not folded. Next unfold continues.";
        unfold_fold ~time:(time+1) transformer goal defs_map f''
      end
;;

let rec get_predicate_set = function
    H.App _ as f ->
    [f]
  | H.Or (f1, f2) ->
     get_predicate_set f1 @ get_predicate_set f2
  | H.And (f1, f2) ->
     get_predicate_set f1 @ get_predicate_set f2
  | _ -> []
;;

let rec get_predicate_set_ex = function
    H.App _ as f ->
    [f]
  | H.Or (f1, f2) ->
     get_predicate_set_ex f1 @ get_predicate_set_ex f2
  | H.And (f1, f2) ->
     get_predicate_set_ex f1 @ get_predicate_set_ex f2
  | H.Exists (_, f) -> get_predicate_set_ex f
  | H.Forall (_, f) -> get_predicate_set_ex f
  | _ -> []
;;

let rec get_permutation = function
    [] -> [[]]
  | x::xs ->
     let xs' = get_permutation xs in
     xs'@(List.map (fun ys -> x::ys) xs')
;;

(*
  [(0,[A]); (1,[B;C])]      [(0,[C]); (1,[D;E])]

  [
    [(0,[A]); (1,[D;E])]
    ...
  ]

  (int * string list) list list
*)

(*
let get_unfold_set all_deps goal_preds f =

  P.pp_formula f |> P.dbgn "Debugged Formula";
  let rec multiply all_deps = function
      [] -> [[]]
    | x::xs ->
       let vss : (int * string list) list = D.find x all_deps in
       let rs : (int * string list) list list = multiply all_deps xs in
       let rs' = List.map (fun (r:(int * string list) list) -> vss@r) rs in
       rs' 
  in
  let get_probable_set all_deps conj =
    let pred_set = get_predicate_set conj |> List.sort_uniq H.compare_raw_hflz |> List.map explode_pred |> List.map fst in
   
    let multiplied_set : (int * string list) list list = multiply all_deps pred_set in
    
    List.filter (fun xs ->
        let ps = List.map snd xs |> List.concat in
        List.for_all (fun p -> List.mem p ps) pred_set
      ) multiplied_set 
  in
  
  let conjuncts = get_conjuncts f in
  P.pp_list P.pp_formula conjuncts |> P.dbg "All Conjuncts";
  
  let conjuncts_set = List.map (fun c -> (c, get_probable_set all_deps c)) conjuncts in
  P.pp_list (fun (f, (a : (int * string list) list list)) -> P.pp_formula f ^ "-> {" ^ (P.pp_list (fun (b:(int * string list) list) -> "^" ^ P.pp_list (fun (d,ss) -> "[" ^ string_of_int d ^ " & " ^ (String.concat "+" ss) ^ "]") b ^ "^") a) ^ "}\n") conjuncts_set |> P.dbgn "Probable Set";
  
  let conjuncts_set' = List.filter (fun (_, xs) ->
                           List.exists (fun ys -> List.length ys >= List.length goal_preds) xs
                           ) conjuncts_set |> List.map fst in
  P.pp_list P.pp_formula conjuncts_set' |> P.dbg "Chosen Set";
  
  List.map (fun conjunct ->
      let pred_set = get_predicate_set conjunct |> List.sort_uniq H.compare_raw_hflz in
      if List.length pred_set > 5 then
        [[]]
      else
        let perm_pred = get_permutation pred_set in
        List.filter ((<>)[]) perm_pred
    ) conjuncts_set' |> List.concat

P.pp_formula f |> P.dbg "f";  

;; *)

let rec get_predicates = function
    H.App _ as f -> [f]
  | H.And (f1, f2) ->
     get_predicates f1 @ get_predicates f2
  | H.Or (f1, f2) ->
     get_predicates f1 @ get_predicates f2
  | _ -> []
;;


let rec auto_rename = function
    H.Var s -> H.Var (s^s)
  | H.Or (f1, f2) -> H.Or (auto_rename f1, auto_rename f2)
  | H.And (f1, f2) -> H.And (auto_rename f1, auto_rename f2)
  | H.Abs (s, f) -> H.Abs (s, auto_rename f)
  | H.App (f1, f2) -> H.App (auto_rename f1, auto_rename f2)
  | H.Op (o, fs) -> H.Op (o, List.map auto_rename fs)
  | H.Pred (o, fs) -> H.Pred (o, List.map auto_rename fs)
  | H.Forall (s, f) -> H.Forall (s, auto_rename f)
  | H.Exists (s, f) -> H.Exists (s, auto_rename f)
  | H.Int _ as f -> f
  | H.Bool _ as f -> f
;;

(*
let rec bf_unfold_fold ?(time=0) ?(unfold_set=[]) all_deps transformer goal defs_map goal_preds f =
      let new_unfold_set = get_unfold_set all_deps goal_preds f in
      P.pp_list (fun xs -> "[" ^ P.pp_list P.pp_formula xs ^ "]") new_unfold_set |> P.dbg "Unfold Set";
      let unfolded_pair_set = List.map (fun x -> (f,x)) new_unfold_set in
      let unfold_set' = unfold_set @ unfolded_pair_set in
      
      match unfold_set' with
        [] -> None
      | (f, pred)::other_preds ->
         P.pp_formula f |> P.dbg "Unfoldable Formula";
         ("[" ^ P.pp_list P.pp_formula pred ^ "]") |> P.dbg "Unfoldable Predicates";
         let f' = controlled_unfold_formula pred defs_map f in
         let f'' = transformer f' in
         let is_matched, f' = fold goal f'' in
         if is_matched then
           begin
             print_endline "Successfully folded..";
             let newpred = mk_rule goal.var goal.H.args goal.fix f' in
             Some [newpred]
           end
         else
           begin
             print_endline "Not folded. Next unfold continues.";
             bf_unfold_fold ~time:(time+1) ~unfold_set:other_preds all_deps transformer goal defs_map goal_preds f''
           end
;;
 *)

let pp_deps (deps : (int * string list) list) =
  let pp_dep (i, ps) = "(" ^ (string_of_int i) ^ ", [" ^ P.pp_list P.id ps ^ "])" in
  P.pp_list pp_dep deps
;;

(*
let rec build_all_deps i path (deps:(string * hfl list) list D.t) (v:string) : (int * string list) list =
  let pred_names_args = D.find v deps in
  let pred_names = List.map fst pred_names_args in
  let pred_names' = List.filter (fun p -> not (List.mem p path)) pred_names in
  if List.length pred_names' > 0 then
    let fn v = build_all_deps (i+1) (path@[v]) deps v in
    let other_dep = List.map (fun p -> fn p) pred_names' |> List.concat in
    (i, pred_names')::other_dep
  else
    []
;;
 *)
(*
let guessed_unfold_fold transformer goal defs_map f =
  let deps : (string * hfl list) list D.t =
    D.fold (fun v f acc ->
        let preds = get_predicate_set f.H.body (* |> List.sort_uniq H.compare_raw_hflz *) in
        let pred_names_args = List.map (fun p -> explode_pred p) preds in
        D.add v pred_names_args acc) defs_map D.empty
  in
  let keys : string list = D.bindings deps |> List.map fst in
  let all_deps : (int * string list) list D.t =
    List.fold_left (fun all_deps key ->
        let all_dep = build_all_deps 1 [] deps key in
        D.add key ((0,[key])::all_dep) all_deps 
      ) D.empty keys
  in
  D.fold (fun k (deps: (int * string list) list) (acc : string) ->
      acc ^ ";\n" ^ k ^ "," ^ (pp_deps deps))
    all_deps "" |> P.dbg "Deps";
  
  bf_unfold_fold all_deps transformer goal defs_map f
;;
 *)

let substitute_args to_be by (args : hfl list) =
  if List.length to_be <> List.length by then
    raise (StrangeSituation "tobe <> by in substitution")
  else
    let temps = get_temps_n (List.length to_be) in
    let subs_pair1 = List.combine to_be (List.map H.mk_var temps) in
    let subs_pair2 = List.combine temps by in
    let subs_arg (arg:hfl) ((to_be:string), (by:hfl)) : hfl = U.subs_var to_be by arg |> AP.normalize in
    List.map (fun arg ->
        let arg' = List.fold_left subs_arg arg subs_pair1 in
        List.fold_left subs_arg arg' subs_pair2
      ) args
;;

(*
let rec build_tree_deps i (path:string list) defs_map (deps:(string * hfl list) list D.t) args (v:string) : (int list * string * hfl list) list =
  let pred_names_args = D.find v deps in
  let params = (D.find v defs_map).H.args |> List.map H.mk_var in
  (* let pred_names = List.map fst pred_names_args in *)
  let pred_names_indices : (int list * string * hfl list) list =
    List.mapi (fun k (p, a) ->
        let to_be = (D.find p defs_map).H.args in
        let args' = substitute_args to_be args a in
        (i@[k],p,args')
      ) pred_names_args
  in
  
  let nonterminals = List.filter (fun (_, p, _) -> not (List.mem p path)) pred_names_indices in
  if List.length nonterminals > 0 then
    let fn k a (v : string) = build_tree_deps k (path@[v]) defs_map deps a v in
    let other_dep = List.map (fun (i, p, a) -> fn i a p) nonterminals |> List.concat in
    pred_names_indices@other_dep
  else
    pred_names_indices
;;

let pp_path_deps (deps : (int list * string * hfl list) list) =
  let pp_dep (i, ps, args) = "(" ^ (P.pp_list ~sep:"" string_of_int i) ^ "," ^ ps ^ ("{" ^ P.pp_list P.pp_formula args ^ "}") ^ ")" in
  "[" ^ P.pp_list pp_dep deps ^ "]"
;;

let get_unfold_path (all_deps : (int list * string * hfl list) list D.t)  f =
  P.pp_formula f |> P.dbgn "Debugged Formula";
  let multiply_two (xs : (int list * string * hfl list) list) (ys : (int list * string * hfl list) list) : (int list * string * hfl list) list list =
    List.map (fun x -> x::ys) xs 
  in
  let rec multiply all_deps = function
      [] -> [[]]
    | x::xs ->
       let rs : (int list * string * hfl list) list list = multiply all_deps xs in
       (* pp_path_deps x |> P.dbg "x"; *)
       let rs' = List.map (fun (r:(int list * string * hfl list) list) -> multiply_two x r) rs |> List.concat in
       (* P.pp_list pp_path_deps rs' |> P.dbg "rs'"; *)
       rs' 
  in
  let get_probable_set (all_deps : (int list * string * hfl list) list D.t) conj =
    let pred_set = get_predicate_set conj |> List.map explode_pred |> List.map fst in
    let all_paths_seperated : (int list * string * hfl list) list list = List.map (fun p ->
                                  let all_paths = D.find p all_deps in
                                  let possible_paths = List.filter (fun (_, p', _) -> List.mem p' pred_set) all_paths in
                                  possible_paths
                                ) pred_set in
    let multiplied_set : (int list * string * hfl list) list list = multiply all_deps all_paths_seperated in
    
    List.filter (fun (xs : (int list * string * hfl list) list) ->
        let ps = List.map (fun (_,a,_) -> a) xs in
        List.for_all (fun p -> List.mem p ps) pred_set
      ) multiplied_set 
  in
  
  let conjuncts = get_conjuncts f in
  P.pp_list P.pp_formula conjuncts |> P.dbg "All Conjuncts";
  let conjuncts_set = List.map (fun c -> (c, get_probable_set all_deps c)) conjuncts in
  
  P.pp_list (fun (f, (a : (int list * string * hfl list) list list)) -> P.pp_formula f ^ "-> { " ^ (P.pp_list ~sep:" ; "pp_path_deps a) ^ " }\n"
    ) conjuncts_set |> P.dbgn "Probable Set";

  
  (* let conjuncts_set' = List.filter (fun (_, xs) ->
                           List.exists (fun ys -> List.length ys >= List.length goal_preds) xs
                           ) conjuncts_set |> List.map fst in
  P.pp_list P.pp_formula conjuncts_set' |> P.dbg "Chosen Set"; *)
  conjuncts_set
  (*List.map (fun conjunct ->
      let pred_set = get_predicate_set conjunct |> List.sort_uniq H.compare_raw_hflz in
      if List.length pred_set > 5 then
        [[]]
      else
        let perm_pred = get_permutation pred_set in
        List.filter ((<>)[]) perm_pred
    ) conjuncts_set |> List.concat
   *)
;;


let rec analyze_bf ?(time=0) ?(unfold_set=[]) all_deps transformer goal defs_map f =
      let new_unfold_set = get_unfold_path all_deps f in
      (* P.pp_list (fun xs -> "[" ^ P.pp_list P.pp_formula xs ^ "]") new_unfold_set |> P.dbg "Unfold Set"; *)
      (* let unfolded_pair_set = List.map (fun x -> (f,x)) new_unfold_set in
      let unfold_set' = unfold_set @ unfolded_pair_set in
      
      match unfold_set' with
        [] -> None
      | (f, pred)::other_preds ->
         P.pp_formula f |> P.dbg "Unfoldable Formula";
         ("[" ^ P.pp_list P.pp_formula pred ^ "]") |> P.dbg "Unfoldable Predicates";
         let f' = controlled_unfold_formula pred defs_map f in
         let f'' = transformer f' in
         let is_matched, f' = fold goal f'' in
         if is_matched then
           begin
             print_endline "Successfully folded..";
             let newpred = mk_rule goal.var goal.H.args goal.fix f' in
             Some [newpred]
           end
         else
           begin
             print_endline "Not folded. Next unfold continues.";
             analyze_bf ~time:(time+1) ~unfold_set:other_preds all_deps transformer goal defs_map goal_preds f''
           end
       *)
      ()
;;
 *)

let pp_path_deps1 (deps : (hfl list * string * hfl list) list) =
  let pp_dep (i, ps, args) = "(" ^ (P.pp_list ~sep:">>" P.pp_formula i) ^ "," ^ ps ^ ("{" ^ P.pp_list P.pp_formula args ^ "}") ^ ")" in
  "[" ^ P.pp_list pp_dep deps ^ "]"
;;

let pp_path_deps2 (pred_times, (deps : (hfl list * string * hfl list) list)) =
  let pp_times (((pred_name, args), times) : ((string * hfl list) * int)) = pred_name ^ " " ^ P.pp_list P.pp_formula args ^ "->" ^ (string_of_int times) in
  let pp_dep (i, ps, args) = "(" ^ (P.pp_list ~sep:">>" P.pp_formula i) ^ "," ^ ps ^ ("{" ^ P.pp_list P.pp_formula args ^ "}") ^ ")" in
  "<" ^ P.pp_list pp_times pred_times ^ "> [" ^ P.pp_list pp_dep deps ^ "]"
;;

let unfold_along_a_path_times defs_map uf_times path_seq f =

  let rec unfold_along_path f = function
      [] -> f
    | node::xs ->
       P.pp_formula node |> P.dbg "To be unfolded";
       let f' = unfold_pred node defs_map f in
       P.pp_formula f' |> P.dbg "f' (after unfolding)";
       unfold_along_path f' xs
  in

  let rec unfold_times f = function
      [] -> f
    | (_, 0)::xs ->
       unfold_times f xs
    | (pred_name, n)::xs ->
       print_endline ("Unfolding " ^ pred_name);
       let f' = unfold_one_pred pred_name defs_map f in
       unfold_times f' ((pred_name, (n-1))::xs)
  in

           
  P.pp_formula f |> P.dbg "Unfolding will take place in";
  let f' =
    if uf_times = 0
    then f
    else if uf_times = 1
    then let f' = unfold_along_path f path_seq in
         f'
    else if List.length path_seq = 1
    then let (pred, _) = U.explode_pred (List.hd path_seq) in
      unfold_times f [(pred, uf_times)]
    else
      raise Err
  in

  f'
;;

let unfold_fold_along_a_path defs_map ((times, path) : (((string * hfl list) * int) list * (hfl list * string * hfl list) list)) f =
  print_endline "\nUnfold Begins\n";
  let rec find_first fn = function
      [] -> raise Not_found
    | x::xs -> if fn x
               then (x, xs)
               else let (x', xs') = find_first fn xs in
                    (x', x::xs')
  in
  
  P.pp_formula f |> P.dbg "formula (conjunct) to unfold";
  pp_path_deps2 (times, path) |> P.dbg "The Path";
  
  let (f',_) = List.fold_left (fun (f, times) (path_seq, pred, _) ->
                   let (_,uf_times), times' = find_first (fun ((pred',_),_) -> pred'=pred) times in
                   
                   let f' = unfold_along_a_path_times defs_map uf_times path_seq f in
                   (f', times')
                 ) (f, times) path
  in
  f'
;;

let unfold_fold_along_paths goal transformer defs_map (unfold_paths : (hfl * (((string * hfl list) * int) list * (hfl list * string * hfl list) list) list) list) f =
  print_endline "\nUnfold+fold Try Begins\n";

  P.pp_formula f |> P.dbg "f";
  let conjuncts = U.get_conjuncts f in
  let rec multiply = function
      [] -> [[]]
    | x::xs ->
       let rs = multiply xs in
       if List.length x = 0 then
         rs
       else
         let rs' = List.map (fun r -> List.map (fun x' -> x'::r) x) rs |> List.concat in
         rs' 
  in
  let possibilities =
    List.fold_left
      (fun acc conjunct ->
        try
          let (_, paths) = List.find (fun (f, _) -> f = conjunct) unfold_paths in
          string_of_int (List.length paths) |> P.dbg "Total paths";
          let f_paths = List.map (fun p -> (conjunct, p)) paths in
          acc @ [f_paths]
        with
          _ -> acc
      ) [] conjuncts
  in
  "[" ^ P.pp_list (fun pos -> List.length pos |> string_of_int) possibilities ^ "]" |> P.dbg "Possibilities"; 
  
  let all_possibilities = multiply possibilities in
  string_of_int (List.length all_possibilities) |> P.dbg "Total possibilities";
  
  let r = List.fold_left (fun acc a_possibility ->
              print_endline "Trying a possibility";
              match acc with
                Some _ -> acc
              | None ->
                 try
                   let conjuncts' =
                     List.map (fun conjunct ->
                         P.pp_formula conjunct |> P.dbg "Conjunct:";
                         try
                           let (_, path) = List.find (fun (f',_) -> f'=conjunct) a_possibility in
                           unfold_fold_along_a_path defs_map path conjunct
                         with
                           Not_found -> conjunct
                         | e -> raise e
                       ) conjuncts in
                   let f' = H.mk_ands conjuncts' |> transformer in
                   let is_matched, f'' = fold goal f' in
                   if is_matched then
                     Some f''
                   else
                     None
                 with
                   _ -> None
            ) None all_possibilities
  in
  r

;;

let rec build_tree_deps1 (prefix:hfl list) (path:string list) defs_map (deps:hfl list D.t) args (v:string) : (hfl list * string * hfl list) list =
  let pred_names_args = D.find v deps in
  let params = (D.find v defs_map).H.args |> List.map H.mk_var in
  (* let pred_names = List.map fst pred_names_args in *)
  let pred_names_indices : (hfl list * string * hfl list) list =
    List.map (fun pred_call ->
        let (p, a) = U.explode_pred pred_call in
        let to_be = (D.find v defs_map).H.args in
        let args' = substitute_args to_be args a in
        (prefix,p,args')
      ) pred_names_args
  in
  
  let nonterminals = List.filter (fun (_, p, _) -> not (List.mem p path)) pred_names_indices in
  if List.length nonterminals > 0 then
    let fn (prefix, p, a) =
      (* let to_be = (D.find p defs_map).H.args in
      let args' = substitute_args to_be args a in *)
      let pred_call' = U.implode_pred p a in
      build_tree_deps1 (prefix@[pred_call']) (path@[p]) defs_map deps a p
    in
    let other_dep = List.map fn nonterminals |> List.concat in
    pred_names_indices@other_dep
  else
    pred_names_indices
;;

let get_times_of_unfold orig_formula target_formula =

  P.pp_formula orig_formula |> P.dbg "Original Formula";
  P.pp_formula target_formula |> P.dbg "Target Formula";
  
  let orig_preds = get_predicates orig_formula in
  let target_preds = get_predicates target_formula in
  let target_preds_args' = List.map U.explode_pred target_preds in

  let find_close pred_name args preds_args =
    let get_rank xs ys =
      if List.length xs <> List.length ys
      then 0
      else let xys = List.map2 (fun x y -> if U.fv x = U.fv y then 1 else 0) xs ys in
           List.fold_left (+) 0 xys
    in
    let rec get_others x = function
        [] -> []
      | y::ys when y=x -> ys
      | y::ys ->
         y::get_others x ys
    in
      
    let preds_args_rank = List.map (fun (pn, a) ->
                              let pr = if pn=pred_name then 1 else 0 in
                              let d = get_rank a args in
                              ((pn, a), d*pr)
                            ) preds_args in
    let max_rank = List.fold_left (fun (x, a) (y, b) -> if b > a then (y, b) else (x, a)) (List.hd preds_args_rank) (List.tl preds_args_rank) in
    let rest = get_others max_rank preds_args_rank in
    fst max_rank, List.map fst rest
  in
  
  let pred_args_pred'args', _ =
    List.fold_left (fun (acc,target_preds_args') predicate ->
        let pred_name, args = U.explode_pred predicate in
        let pred_args', target_preds_args'' = find_close pred_name args target_preds_args' in
        acc@[(pred_name, args, pred_args')], target_preds_args''
      ) ([], target_preds_args') orig_preds
  in (** Original predicate name, arguments, unfolded predicate call *)

  let all_ms_constraints =
    List.mapi
      (fun i (pred_name, org_args, pred_args') ->

        P.pp_list P.pp_formula org_args |> P.dbg "org_args";
        (fun (a,b) -> a ^ " " ^ P.pp_list P.pp_formula b) pred_args' |> P.dbg "pred_args'";
        
        let args' = snd pred_args' in
        
        let args_args' = List.combine org_args args' in
        
        let deltas = List.map (fun (arg, arg') -> AP.normalize (H.Op (Arith.Sub, [arg';arg]))) args_args' in
        let args_args'_deltas = List.combine args_args' deltas in
        let multiplier = (pred_name ^ (string_of_int i)) in

        P.dbg "Multiplier" multiplier;
        
        let multiplied_deltas =
          List.fold_left (fun acc ((arg, arg'), delta) ->
              match delta with
                H.Int _ ->
                 (* P.pp_formula delta |> P.dbg "delta"; *)
                 let t = H.Op (Arith.Mult, [H.Var multiplier; delta]) |> AP.normalize in
                 (* P.pp_formula t |> P.dbg "t"; *)
                 acc @ [(arg, arg', t)]
              | f ->
                 P.pp_formula f |> P.dbg "Exceptions";
                 acc
            ) [] args_args'_deltas in
        
        let constraints =
          List.map (fun (a, _, d) ->
              let aa = auto_rename a in
              let a'_md = (H.Op (Arith.Add, [a;d])) |> AP.normalize in
              H.Pred (Formula.Eq, [aa;a'_md])
            ) multiplied_deltas
        in
        P.pp_list P.pp_formula constraints |> P.dbg "Constraints";
        (((pred_name, org_args), multiplier), constraints)
      ) pred_args_pred'args' in
  let pred_ms, all_constraints = List.split all_ms_constraints in (** Predicates with their multipliers, all constraints *)
  let ms = List.map snd pred_ms in (** Multipliers *)
  let gen_cons = H.Pred (Formula.Gt, [H.Op (Arith.Add, List.map H.mk_var ms); H.Int 0]) in
  
  match List.concat all_constraints with
    [] -> []
  | all ->
     P.pp_list P.pp_formula all |> P.dbg "All";
     let all' = U.reduce_eq ms all in
     P.pp_list P.pp_formula all' |> P.dbg "All'";
     let c = List.fold_left H.mk_and gen_cons all' in
     let model = Z.solve_model_s ms gen_cons all' in
     
     List.iter (fun constraints ->
         P.pp_list P.pp_formula constraints |> P.dbg ""
       ) all_constraints;
           
           
     List.iter (fun (id, v) -> print_endline (id ^ ": " ^ (string_of_int v))) model;
     List.map (fun (pred, m) ->
         let (_, v) =
           try
             List.find (fun (id, _) -> id = m) model
           with
             Not_found ->
             print_endline (m ^ " is not found in the model");
             raise Not_found
         in
         (pred, v)
       ) pred_ms
;;



let get_times_of_unfold_from_paths (possible_paths : (hfl list * string * hfl list) list list) =

  
  let get_times_of_unfold_from_path (path : (hfl list * string * hfl list) list) =

    pp_path_deps1 path |> P.dbg "Path under consideration";
    let org_formula = List.map (fun (a,_,_) -> List.hd a) path |> H.mk_ands in
    let test_formula = List.map (fun (_,b,c) -> U.implode_pred b c) path |> H.mk_ands in
    P.pp_formula test_formula |> P.dbg "Formula to be tested";

    match get_times_of_unfold org_formula test_formula with
      [] -> None
    | pred_times ->
       Some (pred_times, path)
  in

  List.fold_left (fun acc path  ->
      match get_times_of_unfold_from_path path with
        None -> acc
      | Some times_path -> times_path::acc
    ) [] possible_paths
;;

let get_unfold_path1 defs_map (all_deps : (hfl list * string * hfl list) list D.t) f =
  P.pp_formula f |> P.dbgn "Debugged Formula";
  
  let multiply_two (xs : (hfl list * string * hfl list) list) (ys : (hfl list * string * hfl list) list) : (hfl list * string * hfl list) list list =
    List.map (fun x -> x::ys) xs 
  in

  let rec multiply all_deps = function
      [] -> [[]]
    | x::xs ->
       let rs : (hfl list * string * hfl list) list list = multiply all_deps xs in
       (* pp_path_deps x |> P.dbg "x"; *)
       let rs' = List.map (fun (r:(hfl list * string * hfl list) list) -> multiply_two x r) rs |> List.concat in
       (* P.pp_list pp_path_deps rs' |> P.dbg "rs'"; *)
       rs' 
  in

  let update_path param by ((path, last_pred, last_args) : (hfl list * string * hfl list)) =
    let to_be = List.map (function H.Var s -> s | _ -> raise Err) param in
    let path' = List.map (fun node ->
                    let (pn, args) = U.explode_pred node in
                    P.pp_list P.pp_formula args |> P.dbg "args(before)";
                    let args' = substitute_args to_be by args in
                    P.pp_list P.pp_formula args' |> P.dbg "args(after)";
                    U.implode_pred pn args'
                  ) path in
    let last_args' = substitute_args to_be by last_args in
    (path', last_pred, last_args')
  in
  
  let get_probable_set (all_deps : (hfl list * string * hfl list) list D.t) conj =
    let preds = get_predicate_set conj |> List.map U.explode_pred in
    let pred_set = List.map fst preds in
    let all_paths_seperated : (hfl list * string * hfl list) list list =
      List.map (fun (p, args) ->
          P.dbg "Probable set for " p;
          let all_paths = D.find p all_deps in
          let params = (D.find p defs_map).H.args |> List.map H.mk_var in
          let possible_paths = List.filter (fun (_, p', _) -> List.mem p' pred_set) all_paths in
          P.pp_list P.pp_formula args |> P.dbg "args";
          let possible_paths' = List.map (update_path params args) possible_paths in
          possible_paths'
        ) preds in
    let multiplied_set : (hfl list * string * hfl list) list list = multiply all_deps all_paths_seperated in
    
    let paths = List.filter (fun (xs : (hfl list * string * hfl list) list) ->
                    let ps = List.map (fun (_,a,_) -> a) xs in
                    List.for_all (fun p -> List.mem p ps) pred_set
                  ) multiplied_set in

    paths
  in
  
  let conjuncts = U.get_conjuncts f in
  P.pp_list P.pp_formula conjuncts |> P.dbg "All Conjuncts";

  let conjuncts_set = List.map (fun c -> (c, get_probable_set all_deps c)) conjuncts in
  
  P.pp_list (fun (f, (a : (hfl list * string * hfl list) list list)) -> P.pp_formula f ^ "-> { " ^ (P.pp_list ~sep:" ; " pp_path_deps1 a) ^ " }\n"
    ) conjuncts_set |> P.dbgn "Probable Set 1";

  let conjuncts_set' = List.fold_left (fun acc (f, paths)  ->
                           (f, get_times_of_unfold_from_paths paths)::acc
                         ) [] conjuncts_set in

  let conjuncts_set'' = List.map (fun (f, pos_sets) ->
                            let pos_sets'' = 
                              List.filter (fun (a, b) ->
                                  if List.for_all (fun ((pred,_), i) ->
                                         let (c,_,_) = List.find (fun (c,_,_) -> (List.hd c |> U.explode_pred |> fst) = pred) b in
                                         List.length c = 1 || i <= 1) a then
                                    true
                                  else
                                    let sum = List.fold_left (fun acc (_,i) -> acc + i) 0 a in
                                    if sum = 0 then
                                      false
                                    else
                                      true
                                ) pos_sets
                            in
                            let pos_sets' = List.sort_uniq (fun (_, a) (_, b) ->
                                                let la = List.fold_left (fun a (l,_,_) -> a + List.length l) 0 a in
                                                let lb = List.fold_left (fun a (l,_,_) -> a + List.length l) 0 b in
                                                if la < lb then
                                                  -1
                                                else
                                                  1
                                              ) pos_sets'' in
                            (f, pos_sets')
                          ) conjuncts_set' in
  P.pp_list
    (fun (f, (a : (((string * hfl list) * int) list * (hfl list * string * hfl list) list) list)) -> P.pp_formula f ^ "-> { " ^ (P.pp_list ~sep:" ; " pp_path_deps2 a) ^ " }\n"
    ) conjuncts_set'' |> P.dbgn "Probable Set 2";
  conjuncts_set''
;;

let graphed_unfold_fold1 transformer goal defs_map f =
  let deps : hfl list D.t =
    D.fold (fun v f acc ->
        let bd = f.H.body in
        P.pp_formula bd |> P.dbg "BD";
        let preds = get_predicate_set_ex bd (* |> List.sort_uniq H.compare_raw_hflz *) in
        P.pp_list P.pp_formula preds |> P.dbg "PREDS";
        D.add v preds acc) defs_map D.empty
  in
  let keys = D.bindings deps |> List.map fst in
  let all_deps : (hfl list * string * hfl list) list D.t =
    List.fold_left (fun all_deps key ->
        let args = (D.find key defs_map).H.args |> List.map H.mk_var in
        let pred_call = U.implode_pred key args in
        let tree_dep = build_tree_deps1 [pred_call] [key] defs_map deps args key in
        D.add key tree_dep all_deps 
      ) D.empty keys
  in
  D.fold (fun k (deps: (hfl list * string * hfl list) list) (acc : string) ->
      acc ^ ";\n" ^ k ^ " -> " ^ (pp_path_deps1 deps))
    all_deps "" |> P.dbg "Tree Deps";

  let unfold_paths : (hfl * (((string * hfl list) * int) list * (hfl list * string * hfl list) list) list) list = get_unfold_path1 defs_map all_deps f in

  let r = unfold_fold_along_paths goal transformer defs_map unfold_paths f in
(* bf_unfold_fold all_deps transformer goal defs_map f *)
  r
;;



let get_size_change_graph defs_map : ((bytes * (hfl * int * hfl) list)) D.t =
  let is_const = function
      H.Int _ ->
       true
    | _ ->
       false
  in
  let get_int = function H.Int i -> i | _ -> raise (StrangeSituation "Not an Int") in
  let f v =
    let name = v.H.var in
    let params = v.H.args in
    let body = v.H.body in
    let predcalls = get_predicates body in
    if List.length predcalls = 1 then
      let predcall = List.hd predcalls in
      let (pred, args) = U.explode_pred predcall in
      let pars = (D.find pred defs_map).H.args |> List.map H.mk_var in
      let p_a = List.combine pars args in
      (pred, List.fold_left
               (fun acc p ->
                 let p' = H.mk_var p in
                 List.fold_left
                   (fun acc (p, a) ->
                     let r = H.Op (Arith.Sub, [a;p']) |> AP.normalize in
                     if is_const r then
                       (p', get_int r, p)::acc
                     else
                       acc
                   ) acc p_a
               ) [] params)
    else
      begin
        P.pp_formula body |> P.dbg "body";
        raise (StrangeSituation ("More than one pred call: " ^ string_of_int (List.length predcalls)))
      end
  in
  D.map f defs_map

let get_unit_cycle graph defs_map =
  
  let rec make_multipath n org_pred_name (pred, el) =
    if n = 0 then
      List.map (fun (s,_,_) -> (s, [])) el
    else
      let n' = if org_pred_name = pred then n-1 else n in
      let next = D.find pred graph in
      let multipath = make_multipath n' org_pred_name next in
      List.fold_left (fun acc (s,w,d) ->
          try
            let (_, path) = List.find (fun (s', _) -> s'=d) multipath in
            (s, (pred, (w,d))::path)::acc
          with
            Not_found -> acc
        ) [] el
  in
  let rec mkcycle org_pred_name src multipath =
    if List.for_all (fun m -> List.length m = 0) multipath then
      raise (StrangeSituation "All multipath is empty")
    else
      let hds = List.map List.hd multipath in
      let hd_params = List.map (fun (_,(_,a))->a) hds in
      let pred_name = fst (List.hd hds) in
      if src = hd_params && org_pred_name = pred_name then
        List.map (fun (_,(w,d)) -> [(w,d)]) hds, 1
      else
        let tails = List.map List.tl multipath in
        let cycles, n = mkcycle org_pred_name src tails in
        let pairs = List.map2 (fun (_,(w,d)) cycle -> (w,d)::cycle) hds cycles in
        pairs, n+1
  in
  let f org_pred_name (called_pred_name, el) acc =
    let pred = D.find org_pred_name defs_map in
    let params = pred.H.args in
    let empty_multipath = List.map (fun p -> (p, [])) params in
    let multipath = make_multipath (List.length params) org_pred_name (called_pred_name, el) in
    P.pp_list (fun (s, path) -> P.pp_formula s ^ (P.pp_list (fun (_, (w,d)) -> "(" ^ (string_of_int w) ^ "," ^ P.pp_formula d ^ ")") path)) ~sep:"\n" multipath |> P.dbg "Multipath";
    let srcs, paths = List.split multipath in
    let unit_cycles_path, l = mkcycle org_pred_name srcs paths in
    let unit_cycles = List.combine srcs unit_cycles_path in
    P.pp_list (fun (s, path) -> (P.pp_formula s ^ " -> " ^ P.pp_list (fun (w,d) -> "(" ^ (string_of_int w) ^ "," ^ P.pp_formula d ^ ")") path)) ~sep:"\n" unit_cycles |> P.dbg "Unit Cycle";
    D.add org_pred_name (l, unit_cycles) acc
  in
  D.fold f graph D.empty
;;

let get_recursive_groups defs_map f =
  let defs_l = D.bindings defs_map in
  let pred_deps (pn, pred) = pn, pred.H.body
                            |> get_predicates
                            |> List.map U.explode_pred
                            |> List.map fst
  in
  let pred_n_deps = List.map pred_deps defs_l in
  let rec make_rec_groups_of (nm, deps) = function
      [] -> [nm], []
    | pred_n_deps ->
       let dep_preds, non_dep_preds = List.partition (fun (p, _) -> List.mem p deps) pred_n_deps in
       let rec_dep_preds, rest =
         List.fold_left (fun (acc, rest) p ->
             let rec_grp, rest' = make_rec_groups_of p rest in
             (acc @ rec_grp, rest')
           ) ([], non_dep_preds) dep_preds
       in
       (nm::rec_dep_preds), rest
  in
  let rec make_rec_groups = function
      [] -> []
    | h::rest ->
       let grp, rest' = make_rec_groups_of h rest in
       grp::make_rec_groups rest'
  in
  let grps = make_rec_groups pred_n_deps in
  let grp_map = List.fold_left (fun acc g ->
                    List.fold_left (fun acc a -> D.add a g acc) acc g
                  ) D.empty grps in
  let f_preds = get_predicates f |> List.map U.explode_pred |> List.map fst in
  let grps' = List.map (fun grp -> List.filter (fun g -> List.mem g f_preds) grp) grps in
  grps', grp_map
;;

(*
let get_recursive_groups_of_preds grp_map f =
  let pred_calls = get_predicates f in
  let rec_grps = List.map (fun pred ->
                     let (pn, args) = U.explode_pred pred in
                     List.map (fun g -> (pn, args, g)) (D.find pn grp_map)
                   ) pred_calls in
  []
;;


let rec get_perm = function
    [] -> [[]]
  | x::xs ->
     List.map (fun xs -> (x :: xs)) (get_perm xs)
;;

let perm_groups groups =
  let rec cross = function
      [] -> []
    | x::[] ->
       x
    | x::xs ->
       List.map (fun xs' -> List.map (fun x' -> x'@xs') x) (cross xs)
       |> List.concat
  in
  let grp_perms = List.map get_perm groups in
  cross grp_perms
;;
 *)

let get_perm fvs grp_map ls =
  let is_same_grp (_,(nm,_)) nmy =
    List.mem nmy (D.find nm grp_map)
  in

  let ls' : (int * (bytes * hfl list)) list = List.mapi (fun i l -> (i,l)) ls in
  let fvs' = List.map (fun fv -> fv ^ "'") fvs in
  let fvs'' = List.map (fun fv -> H.mk_var fv) fvs' in
  let ls'' = List.map (fun (i, (pn, p_args)) -> (i, (pn, List.map (subs_vars fvs fvs'') p_args))) ls' in
  let rec aux xs =
    match xs with
    [] -> [[]]
  | x::xs ->
     let perms : (int * (bytes * hfl list)) list list = aux xs in
     let res = List.map
       (fun (p: (int * (bytes * hfl list)) list) ->
         List.fold_left (fun acc ((li, (lPn,_)) as l) ->
             (* if is_same_grp x l then *)
             if not (is_same_grp x lPn) || List.exists (fun (pi,_) -> li=pi) p then
               acc
             else
               (l::p)::acc
           ) [] ls'')
       perms
     in
     res |> List.concat
  in
  
  let res : (int * (bytes * hfl list)) list list = (* List.map (fun x -> List.map snd x) *) (aux ls') in
  string_of_int (List.length res) |> P.dbg "Len";
  
  res, ls', fvs'
;;

let get_pre_candidates grp_map f =
  let fvs = U.fv f in
  let pr_ns = get_predicates f |> List.map U.explode_pred in
  let perms, src, fvs = get_perm fvs grp_map pr_ns in
  src, perms, fvs
;;


let get_deltas unit_cycles =
  let sum ws = List.fold_left (+) 0 ws in
  let f (l, cycles) =
    let deltas = List.map (fun (p, path) -> (p, List.map fst path |> sum)) cycles in
    P.pp_list (fun (p, w) -> "(" ^ P.pp_formula p ^ "," ^ string_of_int w ^ ")") deltas |> P.dbg "Deltas";
    (l, deltas)
  in
  D.map f unit_cycles
;;

let get_optimized_constraints defs_map f (deltas : (int * 'a) D.t) =
  (** n_i *)
  let n_P i pn = H.Var ("n_" ^ pn ^ "_" ^ (string_of_int i)) in 
  let pred_calls = get_predicates f in
  (** n_i, P_i, [t_i] *)
  let n_pn_args = List.mapi (fun i pc ->
                      let (pn, args) = U.explode_pred pc in
                      let n_p = n_P i pn in
                      (n_p, pn, args)
                    ) pred_calls in

  let get_coeff arg =
    let fv = U.fv arg in
    if List.length fv >= 1 then
      let x = List.hd fv in
      let (c, _) = AP.cx_d x arg in
      let c' = AP.list_to_sum c |> AP.eval in
      (x, c')
    else
      raise (StrangeSituation ("Zero free variable " ^ (P.pp_formula arg)))
  in
  let n_pn_args_coeff =
    List.map (fun (n_p, pn, args) ->
        let args' = List.map get_coeff args in
        let args'_params = (D.find pn defs_map).H.args
                     |> List.map H.mk_var
                     |> List.combine args'
        in
        (n_p, pn, args'_params)
      ) n_pn_args
  in
  let get_delta pn deltas param =
    D.find pn deltas
                |> snd
                |> List.find (fun (x, _) -> x = param)
                |> snd
  in
  let fn n_p pn ((x, c), param) : (string * (int * hfl * hfl)) list =
    let delta = get_delta pn deltas param in 
    [(x, (delta, n_p, c))]
  (* c x' = c x + delta * n_p
     x' = c x + delta *) 
  in
  
  let cs : (string * (int * hfl * hfl)) list =
    List.map (fun (n_p, pn, args_params) ->
        List.map (fn n_p pn) args_params
        |> List.concat
      ) n_pn_args_coeff |> List.concat in
  let classify acc (x, c) =
    if D.mem x acc then
      let cs = D.find x acc in
      let acc = D.add x (c::cs) acc in
      acc
    else
      D.add x [c] acc
  in
  let classes = List.fold_left classify D.empty cs in
  let constraints_of_a_class _ cs cons =
    if List.length cs = 0 then
      []
    else
      let c_hd = List.hd cs in
      let c_tl = List.tl cs in
      let mk_a_constraint (delta1, n_p1, c1) (delta2, n_p2, c2) =
        [H.Pred (Formula.Eq, [H.Op (Arith.Mult, [H.Int delta1; n_p1; c2]); H.Op (Arith.Mult, [H.Int delta2; n_p2; c1])])]
      in
      cons @ List.map (mk_a_constraint c_hd) c_tl
  in
  let constraints = D.fold constraints_of_a_class classes []
                    |> List.concat
  in
  let mk_mod_constraints (n_p, pn, args_params) =
    let f5 ((x, c), param) =
      let delta = get_delta pn deltas param in
      let n_p' = if delta < 0 then H.mk_op Arith.Mult [n_p; H.Int (-delta)] else H.mk_op Arith.Mult [c; H.Int delta] in
      (* let a1 = if delta < 0 then H.mk_op Arith.Div [c; H.Int (-delta)] else H.mk_op Arith.Div [c; H.Int delta] in *)
      let nc = H.Var (P.pp_formula n_p ^ x) in
      let a2 = H.mk_op Arith.Mult [nc; c] in         
      H.mk_pred Formula.Eq a2 n_p'                 (* nc*(c/{delta}) = n_p *)
    in
    List.map f5 args_params
             
  in
  let mod_constraints = List.map mk_mod_constraints n_pn_args_coeff |> List.concat in
  let multipliers = List.map (fun (n_p, pn, args) -> (n_p, (pn, args))) n_pn_args in
  let hd_constraint = List.map fst multipliers
                      |> H.mk_op Arith.Add 
                      |> H.mk_pred Formula.Le (H.Int 1)
  in
  let l_Ps = D.map fst deltas in
  let all_constraints = constraints@mod_constraints in
  P.pp_list P.pp_formula ~sep:"\n" all_constraints |> P.dbg "Constraints";
  hd_constraint, all_constraints, multipliers, l_Ps
;;


let get_general_constrains defs_map f deltas =
  let preds_f = get_predicates f in
  H.Pred (Formula.Eq, [H.Int 0;H.Int 0]),[],[],D.empty
;;


let get_constraints defs_map f (deltas : (int * 'a) D.t) =
  let rec all_args_one_var f =
    let fn2 arg =
      let fvs = U.fv arg in
      List.length fvs <= 1
    in
    let fn pred =
      let _, args = U.explode_pred pred in
      List.for_all fn2 args
    in
    let preds = get_predicates f in
    List.for_all fn preds
  in
  if all_args_one_var f then
    get_optimized_constraints defs_map f deltas
  else
    get_general_constrains defs_map f deltas
;;


let get_candidate gen_constraint multipliers l_Ps constraints =
  match constraints with
    [] -> []
  | all ->
     let ms = List.map fst multipliers |> List.map P.pp_formula in
     P.pp_list P.pp_formula all |> P.dbg "All";
     let all' = U.reduce_eq ms all in
     P.pp_list P.pp_formula all' |> P.dbg "All'";
     let c = List.fold_left H.mk_and gen_constraint all' in
     let model = Z.solve_model_s ms gen_constraint all' in
                
     List.iter (fun (id, v) -> print_endline (id ^ ": " ^ (string_of_int v))) model;
     let candidates = List.map (fun (m, (pred, args)) ->
         let (_, v) =
           try
             let (id, t) = List.find (fun (id, _) -> H.mk_var id = m) model in
             (id, t * D.find pred l_Ps)
           with
             Not_found ->
             print_endline (P.pp_formula m ^ " is not found in the model");
             raise Not_found
         in
         ((pred, args), v)
       ) multipliers
    in
    P.pp_list (fun ((pn, args), v) -> pn ^ "(" ^ P.pp_list P.pp_formula args ^ ") -=>" ^ string_of_int v) candidates |> P.dbg "Candidate";
    candidates
;;

let get_gen_candidate fvs gen_constraint multipliers s_Ps mod_constraints constraints =
  match constraints with
    [] -> []
  | all ->
     let ms = List.map fst multipliers |> List.map P.pp_formula in
     P.pp_list P.pp_formula all |> P.dbg "All";
     let all' = U.reduce_eq ~fresh:fvs ms all @ mod_constraints in
     P.pp_list P.pp_formula all' |> P.dbg "All'";
     let c = List.fold_left H.mk_and gen_constraint all' in
     let model = Z.solve_model_s ms gen_constraint all' in
                
     List.iter (fun (id, v) -> print_endline (id ^ ": " ^ (string_of_int v))) model;
     let candidates = List.map (fun (m, (pred, args)) ->
         let (_, v) =
           try
             let (id, t) = List.find (fun (id, _) -> H.mk_var id = m) model in
             let (s,l) = D.find (P.pp_formula m) s_Ps in
             (id, s + t * l)
           with
             Not_found ->
             print_endline (P.pp_formula m ^ " is not found in the model");
             raise Not_found
         in
         ((pred, args), v)
       ) multipliers
    in
    P.pp_list (fun ((pn, args), v) -> pn ^ "(" ^ P.pp_list P.pp_formula args ^ ") -=>" ^ string_of_int v) candidates |> P.dbg "Candidate";
    candidates
;;

let get_unfolded_formula defs_map f candidate =
  let rec unfold_cand f v =
    if v = 0 then
      f
    else
      let f' = unfold_formula defs_map f in
      unfold_cand f' (v-1)
  in
  let rec unfold_cand' ((pred, args), v) =
    let pred_call = U.implode_pred pred args in
    pred_call, unfold_cand pred_call v
  in
  let unfolded_candidate : (hfl * hfl) list = List.map unfold_cand' candidate in
  List.fold_left (fun f (pred_call, unfolded) -> U.subs_f pred_call unfolded f) f unfolded_candidate
;;

let is_unfolding_candidate transformer splitter joiner goal defs_map f deltas (src) fvs (dest : (int * (string * hfl list)) list ) =
  let pp = (fun (i, (pn, args)) -> (string_of_int i) ^ "." ^ pn ^ "(" ^ P.pp_list P.pp_formula args ^ ")") in
  P.pp_list pp src |> P.dbg "src";
  P.pp_list pp dest |> P.dbg "dest";
  let src_dest = List.combine src dest in
  let get_next a args =
    let pred = D.find a defs_map in
    let param_args = List.combine pred.H.args args in
    let pred_calls = pred.H.body |> get_predicates in
    if List.length pred_calls = 1 then
      let pred_call = List.hd pred_calls in
      let pred_call' = subs_vars pred.H.args args pred_call (* List.fold_left (fun pc (p,a) -> subs_vars p a pc) pred_call param_args *) in
      U.explode_pred pred_call'
    else
      raise Err
  in
  let rec get_shortest_distance args a b =
    if a = b then
      args, 0
    else
      let next, args = get_next a args in
      let last_args, dist = get_shortest_distance args next b in
      last_args, dist+1
  in
  let get_shortest_distance ((_,(a,args)) as i) ((_,(b,_)) as j) =
    let pred = D.find a defs_map in
    let last_args, dist = get_shortest_distance args a b in
    let param_last_args = List.combine pred.H.args last_args in
    (i, j, dist, param_last_args) in
  let shortest_distances = List.map2 get_shortest_distance src dest in

  List.iter (fun (i,j,l,s) -> pp j ^ ":" ^ P.pp_list (fun (x,y) -> x ^ "->" ^ P.pp_formula y) s ^ " :" ^ (string_of_int l) |> P.dbg (fst (snd i))) shortest_distances;
  let shortest_distances_i = List.mapi (fun n (i,j,d,s) -> (H.mk_var ("N" ^ string_of_int n),i,j,d,s)) shortest_distances in


  
  let make_constraint (n,(_,(src,org_arg)),(_,(dest,args'')), dist, mid_args) =
    let (l, unit_deltas) = D.find dest deltas in
    let args''_mid_args = List.combine args'' mid_args in
    
    let mid_arg_deltas = List.fold_left (fun acc (arg'', (param, arg)) ->
                             try
                               let _, delta = List.find (fun (x,_) -> x=H.Var param) unit_deltas in
                               acc @ [(arg'', arg, delta)]
                             with
                               _ -> acc
                           ) [] args''_mid_args in

    let constraints' =
      List.map (fun (arg'', mid_arg, unit_delta) ->
          (* let delta = get_delta pn deltas param in *)

          let arg_fv = U.fv arg'' in
          let mod_constraint =
            if List.length arg_fv = 1 then
              let x = List.hd arg_fv in
              let (cs, _) = AP.cx_d (List.hd arg_fv) arg'' in
              let c =  AP.list_to_sum cs |> AP.eval in
              if c = H.Int 1 then
                []
              else
                
              let n_p' = if unit_delta < 0 then H.mk_op Arith.Mult [n; H.Int (-unit_delta)] else H.mk_op Arith.Mult [c; H.Int unit_delta] in
              (* let a1 = if delta < 0 then H.mk_op Arith.Div [c; H.Int (-delta)] else H.mk_op Arith.Div [c; H.Int delta] in *)
              let nc = H.Var (P.pp_formula n ^ x) in
              let a2 = H.mk_op Arith.Mult [nc; c] in  
              let mod_constraint = H.mk_pred Formula.Eq a2 n_p' in
              (* let gt_c = H.mk_pred Formula.Ge nc (H.Int 1) in *)
              [mod_constraint]
            else
              []
          in
          let last_arg = H.Op (Arith.Add, [mid_arg; H.Op (Arith.Mult, [n; H.Int unit_delta])]) in (** mid_arg + Ni * unit_dist *)
          let constraint' = H.Pred (Formula.Eq, [arg''; last_arg]) in 
          (constraint', mod_constraint)
        ) mid_arg_deltas
    in
    let constraints, mod_constraints = List.split constraints' in
    let times = H.Op (Arith.Add, [H.Int dist; H.Op (Arith.Mult, [H.Int l;n])]) in
    src |> P.dbg "source";
    dest |> P.dbg "Dest";
    P.pp_formula n |> P.dbg "n";
    P.pp_formula times |> P.dbg "times";
    P.pp_list P.pp_formula constraints |> P.dbg "constraints";
    (((P.pp_formula n, (dist, l)), (n, (src, org_arg))), (constraints, List.concat mod_constraints)) 
  in
  let sorter ord xs =
    P.pp_list (string_of_int) ord |> P.dbg "Ord";
    P.pp_list P.pp_formula xs |> P.dbg "xs";
    if List.length ord <> List.length xs then
      raise Err;
    
    let ord_xs = List.combine ord xs in
    let sorted_xs = List.sort (fun (i,_) (j,_) -> i-j) ord_xs in
    List.map snd sorted_xs  
  in
  let all_constraints = List.map make_constraint shortest_distances_i in
  let all, constraints' = List.split all_constraints in
  let src_times, ns = List.split all in

  (* let l_Ps = D.map (fun d -> (fst d)) deltas in *)
  let s_Ps = List.fold_left (fun acc (p, sl) -> D.add p sl acc) D.empty src_times in

  let ss = D.fold (fun _ (s,_) acc -> acc+s) s_Ps 0 in
  
  let gen_constraint = List.map fst ns
                       |> H.mk_op Arith.Add
                       |> (fun x -> H.mk_op Arith.Add ([H.Int ss;x])) 
                       |> H.mk_pred Formula.Le (H.Int 1)
  in
  try
    let constraints, mod_constraints = List.split constraints' in
    let candidate = get_gen_candidate fvs gen_constraint ns s_Ps (List.concat mod_constraints) (List.concat constraints) in
    P.pp_formula f |> P.dbg "f";
    let unfolded = get_unfolded_formula defs_map f candidate in
    P.pp_formula unfolded |> P.dbg "unfolded";
    let f'' = transformer unfolded in
    let ord = List.map fst dest in
    P.pp_formula goal.H.body |> P.dbg "Body";
    let goal_body = goal.H.body |> splitter |> sorter ord |> joiner in
    P.pp_formula goal_body |> P.dbg "Sorted Body";
    P.pp_formula f'' |> P.dbg "f''";
    let goal = {H.var=goal.var; args=goal.args; fix=goal.fix; body=goal_body} in (* mk_rule goal.H.var goal.H.args goal.H.fix goal_body in *)
    let is_matched, f' = fold goal f'' in
    if is_matched then
      true, Some f'
    else
      false, None
  with
    _ ->
    P.dbg "Ststus" "Exception";
    false, None 
;;

let get_unfolding_candidates transformer splitter joiner goal defs_map f deltas src fvs perms =
  let rec aux f = function
      [] -> None
    | x::xs ->
       let b,r = f x in
       if b then
         r
       else
         aux f xs
  in

  aux (is_unfolding_candidate transformer splitter joiner goal defs_map f deltas src fvs) perms
;;

let size_change_graphed_unfold_fold transformer splitter joiner goal defs_map f =
  print_endline "----- SIZE Change GRAPH -----";
  let graph = get_size_change_graph defs_map in
  D.iter (fun v (xx,l) -> print_endline xx; List.iter (fun (x, w, y) -> (v ^ " -> (" ^ P.pp_formula x ^ "," ^ string_of_int w ^ "," ^ P.pp_formula y ^ ")" ) |> P.dbg "edge") l) graph;
  let unit_cycles = get_unit_cycle graph defs_map in
  let deltas = get_deltas unit_cycles in
  let _, grp_map = get_recursive_groups defs_map f in
  let src, perms, fvs = get_pre_candidates grp_map f in
  let res = get_unfolding_candidates transformer splitter joiner goal defs_map f deltas src fvs perms in
  
  (* P.pp_list (fun a -> "{" ^ P.pp_list (fun (i,b) -> (string_of_int i) ^ "." ^ P.pp_formula b) a ^ "}\n") perms |> P.dbg "Perm"; *)
  (*
  let gen_constraint, constraints, multipliers, l_Ps = get_constraints defs_map f deltas in
  let candidate = get_candidate gen_constraint multipliers l_Ps constraints in *)
  (*let unfolded = get_unfolded_formula defs_map f candidate in
  let f'' = transformer unfolded in
  let is_matched, f' = fold goal f'' in
  if is_matched then
    begin
      Some f'
      (* let fv_f' = U.fv f' in
      let params = List.filter (fun v -> List.mem v fv_f') goal.H.args in

      let newpred = mk_rule goal.var params goal.fix f' in
      Some ([newpred], params) *)
    end
  else
    None *)
  res
;;

(*
let graphed_unfold_fold transformer goal defs_map f =
  let deps : (string * hfl list) list D.t =
    D.fold (fun v f acc ->
        let preds = get_predicate_set f.H.body (* |> List.sort_uniq H.compare_raw_hflz *) in
        let pred_names_args = List.map (fun p -> explode_pred p) preds in
        D.add v pred_names_args acc) defs_map D.empty
  in
  let keys = D.bindings deps |> List.map fst in
  let all_deps : (int list * string * hfl list) list D.t =
    List.fold_left (fun all_deps key ->
        let args = (D.find key defs_map).H.args |> List.map H.mk_var in
        let tree_dep = build_tree_deps [] [key] defs_map deps args key in
        D.add key tree_dep all_deps 
      ) D.empty keys
  in
  D.fold (fun k (deps: (int list * string * hfl list) list) (acc : string) ->
      acc ^ ";\n" ^ k ^ " -> " ^ (pp_path_deps deps))
    all_deps "" |> P.dbg "Tree Deps";

  analyze_bf all_deps transformer goal defs_map f;
(* bf_unfold_fold all_deps transformer goal defs_map f *)
  ()
;;
 *)

let solve_conflict f defs_map pred_args_body =
  List.map (fun (a,b,c,_) -> (a,b,c)) pred_args_body, defs_map, f

(* let rec resolve i f acc defs_map = function
      [] -> [], defs_map, f
    | (pred_name, args, body, call)::xs ->
       let res, defs_map', f' = resolve (i+1) f (pred_name::acc) defs_map xs in
       if List.mem pred_name acc then
         let new_name = pred_name ^ "_D_" ^ (string_of_int i) in
         let _, args = explode_pred call in
         let new_call = U.implode_pred new_name args in
         let f'' = U.subs_f call new_call f' in
         let body' = U.subs_var pred_name (H.Var new_name) body in
         let pred = D.find pred_name defs_map in
         let new_rule = mk_rule new_name pred.H.args pred.H.fix body' in
         (new_name, args, body')::res, D.add new_name new_rule defs_map', f''
       else
         (pred_name, args, body)::res, defs_map', f'
  in
  resolve 0 f [] defs_map pred_args_body *)
;;

let guess_based_unfold_fold transformer splitter joiner goal defs_map f =
  print_endline "----- GUESSED UNFOLD >> FOLD -----";
  let f' = size_change_graphed_unfold_fold transformer splitter joiner goal defs_map f in
  (* let f' = graphed_unfold_fold1 transformer goal defs_map f in *)
  match f' with
    None -> None
  | Some f'' ->
     let fv_f'' = U.fv f'' in
     let params = List.filter (fun v -> List.mem v fv_f'') goal.H.args in
     let newpred = mk_rule goal.var params goal.fix f'' in
     P.pp_rule newpred |> P.dbg "RULE()";
     Some ([newpred],params)
;;
    
(* let controlled_unfold_fold transformer goal defs_map f =

  print_endline "----- CONTROLLED UNFOLD >> FOLD -----";
  P.pp_formula f |> P.dbg "The Original Formula";
  let pred_calls = get_predicates f in
 
  P.pp_list P.pp_formula pred_calls |> P.dbg "Preds";
  let target_formula = List.map (exec_unfold defs_map) pred_calls |> H.mk_ands in
  
  P.pp_formula f |> P.dbg "The Unfolded Formula";

  (* if List.length pred_calls < 2 then
        begin
          print_endline "Old School Method (Less than 2 predicate calls)";
          unfold_fold transformer goal defs_map' f'
        end
      else *)
  begin
    let goal_preds = get_predicate_set f |> List.map U.explode_pred |> List.map fst in
    match get_times_of_unfold f target_formula with
        [] -> unfold_fold transformer goal defs_map f
      | pred_times' ->
         try
           let pred_times = List.map (fun ((d,_),b) -> (d,b)) pred_times' in
           let rec unfold_times f = function
               [] -> f
             | (_, 0)::xs ->
                unfold_times f xs
             | (pred_name, n)::xs ->
                print_endline ("Unfolding " ^ pred_name);
                let f' = unfold_one_pred pred_name defs_map f |> transformer in
                unfold_times f' ((pred_name, (n-1))::xs)
           in
           
           let f' = unfold_times f pred_times in
           P.pp_formula f' |> P.dbg "The Unfolded";
           let f'' = transformer f' in
           P.pp_formula f'' |> P.dbg "The Transformed";
           P.pp_rule goal |> P.dbg "The Goal";
           let is_matched, f' = fold goal f'' in
           
           if is_matched then
             begin
               print_endline "Successfully folded..";
               let fv_f' = U.fv f' in
               let params = List.filter (fun v -> List.mem v fv_f') goal.H.args in
               let newpred = mk_rule goal.var params goal.fix f' in
               P.pp_rule newpred |> P.dbg "RULE()";
               Some ([newpred], params)
             end
           else
             begin
               print_endline "Not folded. Next unfold continues.";
               unfold_fold transformer goal defs_map f
                           (* raise (Z.TestFailException "") *)
             end
         with
         | Not_found ->
            print_endline "Old School Method (Model is incomplete)";
            unfold_fold transformer goal defs_map f
         | Z.Z3Unsat ->
            print_endline "Old School Method (Unsat Model)";
            raise NotFoldable
         | Z.NoModel ->
            print_endline "Old School Method (No Model)";
            guess_based_unfold_fold transformer goal defs_map f
                                    (* guessed_unfold_fold transformer goal defs_map goal_preds f *)
  end 
;; *)

let concise (r, f) _ =
  (r, f)
;;

let uf = guess_based_unfold_fold (* controlled_unfold_fold *);;
(* let uf = unfold_fold ;; *)

let process_r r f env predname =
    match r with
    Some (r, params, rest, joiner) ->
     print_endline "Folded!!!";
     let vparams = List.map H.mk_var params in
     let f = U.implode_pred predname vparams in
     concise (Some r, joiner (f::rest)) env
    | None ->
       print_endline "Not Folded!!!";
     None, f
;;

let rec exists_elim goal defs_map env f =
  P.pp_formula f |> P.dbg "f in Exists_Elim";
  match f with
  | H.Exists _ as f ->
     begin
       let (qvs, f1') = get_qvs_and_body f in
       let (res2, f') = exec_exists_elim goal defs_map qvs env f1' in
       res2, f'
     end
  | _ -> (None, f)

and exec_exists_elim goal defs_map qvs env f =
    let (f',qvs') = List.fold_left (fun (f, qvs') qv ->
                        let f', b = find_constraint qv f in
                        if b then
                          (f', qvs')
                        else
                          (f, qv::qvs')
                      ) (f,[]) qvs in
    
    let qvs'' = List.filter (fun qv -> is_in qv f') qvs' in
    P.pp_formula f' |> P.dbg "f after possible qv elimination";
    (* if List.length qvs'' > 0 then *)
      let predname, p_a, _, _ = predicate_for_exists goal in
      step2 qvs'' f' defs_map p_a env predname
    (* else
      None, f' *)
      
and step2 qvs f defs_map p_a env predname =
  let fvs = fv f in
  let p_a' = reduce_args qvs p_a in
  let p_a' = List.filter (fun (p,_) -> List.for_all (fun s -> p<>s) qvs && List.mem p fvs) p_a' in
  let ps, _ = List.split p_a' in
  let body' = normalize_exists qvs f in
  let goalpred = mk_rule predname ps Fixpoint.Least body' in
  
  let transformer f = f
                      (* |> unfold_formula defs_map *)
           |> normalize_exists qvs
  in
  (* (fun x-> P.pp_formula goalpred.H.body |> P.dbg "ID splitter @"; [x])*)
  let r = uf transformer U.get_conjuncts H.mk_ands goalpred defs_map f in
  let r' =
    match r with
      Some (r, p) ->
       let r' = Some (r, p, [], H.mk_ands) in
       r'
    | None -> None
  in
  process_r r' f env predname

and normalize_exists qvs f =
  let f' = f
           |> dnf_of_formula
           |> unsat_elim
           |> ex_dist2 qvs
           |> taut_elim         
  in
  P.pp_formula f' |> P.dbg "Normalized";
  f'

and use_constraint qvs f =
     let f' = cnf_of_formula f in
     let (f',qvs') = List.fold_left (fun (f, qvs') qv ->
                        let f', b = find_constraint qv f in
                        if b then
                          (f', qvs')
                        else
                          (f, qv::qvs')
                       ) (f',[]) qvs in
     (f',qvs')

and ex_dist2 qvs f =
  let rec aux s = function
    | H.Pred _ as f when is_in s f ->
       H.Exists (s, f)
    | H.App _ as f when is_in s f -> H.Exists (s, f)
    | H.Or (f1, f2) -> H.Or (aux s f1, aux s f2)
    | H.And _ as f ->
       let (f', qvs') = f |> use_constraint [s] in
       let fs = f' |> cnf_of_formula |> U.get_conjuncts in (** Optimization Point  *)
       let is_ins, not_ins = List.partition (is_in s) fs in
       let is_ins'' =
         if List.length qvs' = 0 then
           is_ins
         else
           List.map (aux s) is_ins
       in       
       let is_ins' = List.filter (fun isin -> not (is_taut isin)) is_ins'' in
       let is_in' = mk_ands is_ins' in
       let not_in' = mk_ands not_ins in
       let f' = mk_ands (not_ins @ is_ins') in
       f'
    | H.Exists (s1, f) ->
       begin
         let f' = aux s f in
         match f' with
           H.Exists (s2, f) ->
           H.Exists (s2, aux s1 f)
         | _ ->
            aux s1 f'
       end
    | f ->
       f
  in
  let f' = List.fold_left (fun f s ->
               let f' = aux s f in
               f'
             ) f qvs in
  f'
;;

let rec is_non_pred = function
  | H.App _ -> false
  | _ -> true
;;

let get_fix_op defs_map f =
  let pred = get_pred defs_map f in
  pred.H.fix
;;  

let rec reduce fn acc = function
    [] -> acc
  | x::xs ->
     let xs' = List.filter (fn x) xs in
     let acc' = List.filter (fn x) acc in
     reduce fn (x::acc') xs'
;;

let rec subset xs ys =
  let r =
    List.for_all (fun x ->
        let r = List.exists (fun y -> y=x) ys in
        r
      ) xs
  in
  r
;;

let reduce_conj f =
  let fs = U.get_conjuncts f in
  let fn x y =
    let dx = U.get_disjuncts x in
    let dy = U.get_disjuncts y in
    not (subset dx dy)
  in
  let fs' = reduce fn [] fs in
  let f' = mk_ands fs' in
  P.pp_formula f' |> P.dbg "Reduced conjuncts";
  f'
;;

let reduce_disj f =
  let fs = U.get_disjuncts f in
  let fn x y =
    let dx = U.get_conjuncts x in
    let dy = U.get_conjuncts y in
    not (subset dx dy)
  in
  let fs' = reduce fn [] fs in
  let f' = mk_ors fs' in
  P.pp_formula f' |> P.dbg "Reduced conjuncts";
  f'
;;

let rec no_const = function
    H.Var _ -> true
  | H.Int _ -> false
  | H.App (f1, f2) -> no_const f1 && no_const f2
  | H.Pred (_, fs) -> List.for_all no_const fs
  | H.Abs (_, fs) -> no_const fs
  | H.Op (_, fs) -> List.exists no_const fs
  | H.Exists (_, f) -> no_const f
  | H.Forall (_, f) -> no_const f
  | H.Bool _ -> false
  | H.And (f1, f2) -> no_const f1 && no_const f2
  | H.Or (f1, f2) -> no_const f1 && no_const f2
;;

let unfold_fold_common transformer goal defs_map f splitter joiner =
  let xs = splitter f in
  let xs', rest = List.partition no_const xs in
  let f' = joiner xs' in

  P.pp_rule goal |> P.dbg "RULE";
  
  let gs = splitter goal.H.body in
  let gs', rest2 = List.partition no_const gs in
  let goalbody' = joiner gs' in
  let goal' = mk_rule (goal.H.var) goal.H.args goal.H.fix goalbody' in
  P.pp_rule goal' |> P.dbg "RULE'";
  let r = uf transformer splitter joiner goal' defs_map f' in
  match r with
    Some (r, f'') ->
     Some (r, f'', rest2, joiner)
  | None ->
    None
;;

let rec unfold_fold_conj goal defs_map f =
  let transformer f = f |> dnf_of_formula |> unsat_elim |> taut_elim |> reduce_disj in
  unfold_fold_common transformer goal defs_map f U.get_conjuncts H.mk_ands
;;

let rec unfold_fold_disj goal defs_map f =
  let transformer f = f |> cnf_of_formula |> unsat_elim |> taut_elim |> reduce_conj in
  unfold_fold_common transformer goal defs_map f U.get_disjuncts H.mk_ors
;;

let rec unfold_fold_exists goal defs_map env = function
    H.And (f1, f2) ->
     let r1, f1' = unfold_fold_exists goal defs_map env f1 in
     let r2, f2' = unfold_fold_exists goal defs_map env f2 in
     concat_option r1 r2, H.And (f1', f2')
  | H.Or (f1, f2) ->
     let r1, f1' = unfold_fold_exists goal defs_map env f1 in
     let r2, f2' = unfold_fold_exists goal defs_map env f2 in
     concat_option r1 r2, H.Or (f1', f2')
  | H.Exists _ as f ->
     exists_elim goal defs_map env f
     |> snd_apply normalize
  | f -> None, f
;;

let rec transform_disjunction goal defs_map env f =
  P.pp_formula f |> P.dbg "f (in disjunction)";
  let fs = U.get_disjuncts f in
  (string_of_int (List.length fs)) |> P.dbg "|disjuncts|";
  let (preds, fs') = List.fold_left
              (fun (acc, fs) f ->
                let (r, f') = transform goal defs_map env f in
                P.pp_formula f' |> P.dbg "TRANSFORMED f";
                concat_option acc r, fs@[f']
              ) (None, []) fs in
  let defs_map' = match preds with
      None -> defs_map
    | Some xs ->
       List.fold_left (fun acc x -> D.add x.H.var x acc) defs_map xs
  in

  P.pp_list P.pp_formula fs |> P.dbg "Temp";
  let atomics, nonatomics = List.partition is_non_pred fs' in
  let new_preds, body =
    match nonatomics with
      _::_::_ ->
       let fixes = List.map (get_fix_op defs_map') nonatomics in
       let fix =
         if List.exists ((=) Fixpoint.Greatest) fixes then
           Fixpoint.Greatest
         else
           Fixpoint.Least
       in
       let f = nonatomics |> (* List.sort compare_raw_hflz |> *) mk_ors in
       let newgoalname = new_predicate_name () in
       let args = List.map H.mk_var goal.H.args in
       let ps = goal.H.args in

       let newgoal = {H.var=newgoalname; args=ps; fix=fix; body=f} in
       let r = unfold_fold_disj newgoal defs_map' f in
       process_r r f env newgoalname
    (* | x::y::[] ->
       let xfix = get_fix_op defs_map' x in
       let yfix = get_fix_op defs_map' y in
       let fix =  if xfix = Fixpoint.Greatest || yfix = Fixpoint.Greatest
                  then Fixpoint.Greatest
                  else Fixpoint.Least
       in
       let f = [x; y] |> List.sort_uniq compare_raw_hflz |> mk_ors in
       
       let newgoalname = new_predicate_name () in
       let args = List.map H.mk_var goal.H.args in
       let ps = goal.H.args in

       let newgoal = {H.var=newgoalname; args=ps; fix=fix; body=f} in
       let r = unfold_fold_disj newgoal defs_map' f in
       let f' = U.implode_pred newgoalname args in
       concise (r, f') env *)
    | [f] -> None, f
    | _ -> None, H.Bool false
  in
  let atomic = mk_ors atomics in
  let f' =
    if List.length atomics = 0 then
      body
    else if List.length nonatomics = 0 then
      atomic
    else
      let f' = mk_ors [atomic; body] in
      f'
  in
  (concat_option new_preds preds, f')
    
and transform_conjunction goal defs_map env f =
  let fs = U.get_conjuncts f in
  let (preds, fs') = List.fold_left
              (fun (acc, fs) f ->
                let (r, f) = transform goal defs_map env f in
                concat_option acc r, fs@[f]
              ) (None, []) fs in
  let defs_map' = match preds with
      None -> defs_map
    | Some xs ->
       List.fold_left (fun acc x -> D.add x.H.var x acc) defs_map xs
  in
  let atomics, nonatomics = List.partition is_non_pred fs' in
  let new_preds, body =
    match nonatomics with
      x::y::[] ->
       let xfix = get_fix_op defs_map' x in
       let yfix = get_fix_op defs_map' y in
       let fix =  if xfix = Fixpoint.Greatest || yfix = Fixpoint.Greatest
                  then Fixpoint.Greatest
                  else Fixpoint.Least
       in
       let f = [x; y] |> (* List.sort compare_raw_hflz |> *) mk_ands in
       
       let newgoalname = new_predicate_name () in
       let args = List.map H.mk_var goal.H.args in
       let ps = goal.H.args in

       let newgoal = {H.var=newgoalname; args=ps; fix=fix; body=f} in
       let r = unfold_fold_conj newgoal defs_map' f in
       
       process_r r f env newgoalname
    | [f] -> None, f
    | _ -> None, H.Bool false
  in
  let atomic = mk_ors atomics in
  let f' =
    if List.length atomics = 0 then
      body
    else if List.length nonatomics = 0 then
      atomic
    else
      let f' = mk_ands [atomic; body] in
      f'
  in
  (concat_option new_preds preds, f')
  
and transform_existential goal defs_map env f =
  P.pp_formula f |> P.dbg " f";
  let qvs, f' = get_qvs_and_body f in
  P.pp_formula f' |> P.dbg " f'";
  
  let rec mk_exists f = function
      [] -> f
    | x::xs -> H.Exists (x, mk_exists f xs)
  in
  let rec distribute = function
      H.Or (f1, f2) ->
      let f1' = distribute f1 in
      let f2' = distribute f2 in
      H.Or (f1', f2')
    | f ->
       let fvs = U.fv f in
       let qvs' = List.filter (fun x -> List.mem x fvs) qvs in
       mk_exists f qvs'
  in
  let f'' = f' |> distribute |> taut_elim |> unsat_elim in
  begin
    let f''' = unfold_fold_exists goal defs_map env f'' in
    print_endline "Transformation of Existential is finished";
    P.pp_formula (snd f''') |> P.dbg " After Existential Transformation";
    f'''
    end
  
and transform goal defs_map env = function
    H.Exists _ as f ->
    let f' = transform_existential goal defs_map env f in
    f'
  | H.Or _ as f ->
     let f' = transform_disjunction goal defs_map env f in
     f'
  | H.And _ as f ->
     let f' = transform_conjunction goal defs_map env f in
     f'
  | f ->
     None, f
;;
    
let transform_hes (defs : H.hes) goal env =
  let defs_map = make_def_map defs in (** List to Map.Make *)
  print_endline "~*~*~*~*~*~*~*~*~*~*~*";
  P.pp_formula goal.H.body |> P.dbg "Goal";
  
  let newpreds, body' = transform goal defs_map env goal.H.body in
  
  let goal_pred = {H.var=goal.H.var; args=goal.args; fix=goal.fix; body=body'} in
  match newpreds with
    Some xs -> goal_pred :: xs @ defs
  | None -> goal_pred ::defs
;;
