open Hflmc2_syntax
   
module H = Raw_hflz
module F = Formula
module A = Arith

module P = Printer
module Z = Z3Interface
module U = MatchMaker
         
module D = Map.Make(String)
module AP = ArithmeticProcessor

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

let rec get_conjuncts = function
    H.And (f1, f2) ->
     let f1' = get_conjuncts f1 in
     let f2' = get_conjuncts f2 in
     f1' @ f2'
  | f ->
     [f]
;;

let rec get_disjuncts = function
    H.Or (f1, f2) ->
     let f1' = get_disjuncts f1 in
     let f2' = get_disjuncts f2 in
     f1' @ f2'
  | f ->
     [f]
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
  let f' = mk f |> get_conjuncts |> List.sort_uniq compare_raw_hflz |> mk_ands in
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
  let f' = mk f |> get_disjuncts |> List.sort_uniq compare_raw_hflz |> mk_ors in
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

let explode_pred f =
  let rec aux acc = function
      H.App (f1, f2) ->
       aux (f2::acc) f1
    | H.Var s -> s, acc
    | f ->
       P.pp_formula f |> P.dbg "ERROR";
       raise (StrangeSituation "Unsupported Predicate Naming")
  in
  let r = aux [] f in
  r
;;

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

let exec_unfold_ext defs_map f =
  let res : (string * H.raw_hflz list) = try explode_pred f with e -> print_endline "exec_unfold"; raise e in
  let f (pred_name, args) =
    let pred = try
        D.find pred_name defs_map
      with e ->
        print_int (D.cardinal defs_map); 
        print_endline pred_name; raise e in
    let params : string list = pred.H.args in
    let temps = get_temps_n (List.length args) in
    let vtemps = List.map (fun t -> H.Var t) temps in
  
    let body' = subs_vars params vtemps pred.H.body in
    let body'' = subs_vars temps args body' in
    (pred_name, args, body'', f)
  in
  f res
;;

let exec_unfold defs_map f =
  let (_, _, body, _) = exec_unfold_ext defs_map f in
  body
;;

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
    | H.App _ when fst (explode_pred f) = pred_name ->
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
    let (p, args) = explode_pred f in
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
      let newpred = mk_rule goal.var goal.H.args goal.fix f' in
      Some [newpred]
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

let get_unfold_set all_deps f =

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
  let conjuncts_set = List.map (fun c -> (c, get_probable_set all_deps c)) conjuncts in

  
  let conjuncts_set' = List.filter (fun (_, xs) -> List.length xs > 0) conjuncts_set |> List.map fst in

  List.map (fun conjunct ->
      let pred_set = get_predicate_set conjunct |> List.sort_uniq H.compare_raw_hflz in
      if List.length pred_set > 10 then
        [[]]
      else
        let perm_pred = get_permutation pred_set in
        List.filter ((<>)[]) perm_pred
    ) conjuncts_set' |> List.concat
  
;;

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

let rec bf_unfold_fold ?(time=0) ?(unfold_set=[]) all_deps transformer goal defs_map f =
      let new_unfold_set = get_unfold_set all_deps f in
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
             bf_unfold_fold ~time:(time+1) ~unfold_set:other_preds all_deps transformer goal defs_map f''
           end
;;

let pp_deps (deps : (int * string list) list) =
  let pp_dep (i, ps) = "(" ^ (string_of_int i) ^ ", [" ^ P.pp_list P.id ps ^ "])" in
  P.pp_list pp_dep deps
;;

let rec build_all_deps i path (deps:(string * H.raw_hflz list) list D.t) (v:string) : (int * string list) list =
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

let guessed_unfold_fold transformer goal defs_map f =
  let deps : (string * H.raw_hflz list) list D.t =
    D.fold (fun v f acc ->
        let preds = get_predicate_set f.H.body |> List.sort_uniq H.compare_raw_hflz in
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
  

let controlled_unfold_fold transformer goal defs_map' f' =
  
  let are_all_pred_same_to =
    let is_pred_same pred_name (pr,_) = pr = pred_name in
    let are_pred_same_to (pred_name,_,pred'_args') =
      List.for_all (is_pred_same pred_name) pred'_args'
    in
    List.for_all are_pred_same_to
  in
  
  print_endline "----------";
  P.pp_formula f' |> P.dbg "The Formula";
  let pred_calls = get_predicates f' in   
  P.pp_list P.pp_formula pred_calls |> P.dbg "Preds";

  if List.length pred_calls < 2 then
        begin
          print_endline "Old School Method (Less than 2 predicate calls)";
          unfold_fold transformer goal defs_map' f'
        end
      else
  begin
    let pred_args_body' = List.map (exec_unfold_ext defs_map') pred_calls in
    let pred_args_body, defs_map, f = solve_conflict f' defs_map' pred_args_body' in
    P.pp_formula f |> P.dbg "The Formula (resolved)";
    let pred_args_pred'args' = List.map (fun (pred_name, args, body) ->
                                   let pred_calls = get_predicates body in
                                   let pred_args' = List.map explode_pred pred_calls in
                                   (pred_name, args, pred_args')
                                 ) pred_args_body in
    if are_all_pred_same_to pred_args_pred'args' then
      let all_ms_constraints = List.mapi (fun i (pred_name, args, pred_args') ->
                                   let args' = snd (List.hd pred_args') in
                                   let args_args' = List.combine args args' in
                                   let deltas = List.map (fun (arg, arg') -> AP.normalize (H.Op (Arith.Sub, [arg';arg]))) args_args' in
                                   let args_args'_deltas = List.combine args_args' deltas in
                                   let multiplier = (pred_name ^ (string_of_int i)) in
                                   
                                   let multiplied_deltas = List.fold_left (fun acc ((arg, arg'), delta) ->
                                                               
                                                               match delta with
                                                                 H.Int _ ->
                                                                  (* P.pp_formula delta |> P.dbg "delta"; *)
                                                                  let t = H.Op (Arith.Mult, [H.Var multiplier; delta]) |> AP.normalize in
                                                                  (* P.pp_formula t |> P.dbg "t"; *)
                                                                  acc @ [(arg, arg', t)]
                                                               | _ -> acc
                                                             ) [] args_args'_deltas in
                                   let constraints = List.map (fun (a, _, d) ->
                                                         let aa = auto_rename a in
                                                         let a'_md = (H.Op (Arith.Add, [a;d])) |> AP.normalize in
                                                         H.Pred (Formula.Eq, [aa;a'_md])
                                                       ) multiplied_deltas in
                                   ((pred_name, multiplier), constraints)
                                 ) pred_args_pred'args' in
      let pred_ms, all_constraints = List.split all_ms_constraints in
      let ms = List.map snd pred_ms in
      let gen_cons = H.Pred (Formula.Gt, [H.Op (Arith.Add, List.map H.mk_var ms); H.Int 0]) in
      match List.concat all_constraints with
        [] -> unfold_fold transformer goal defs_map f
      | all ->
         try
           P.pp_list P.pp_formula all |> P.dbg "All";
           let all' = U.reduce_eq ms all in
           P.pp_list P.pp_formula all' |> P.dbg "All'";
           let c = List.fold_left H.mk_and gen_cons all' in
           let model = Z.solve_model_s ms gen_cons all' in
           
           List.iter (fun constraints ->
               P.pp_list P.pp_formula constraints |> P.dbg ""
             ) all_constraints;
           
           List.iter (fun (id, v) -> print_endline (id ^ ": " ^ (string_of_int v))) model;
           let pred_times = List.map (fun (pred_name, m) ->
                                let (_, v) =
                                  try
                                    List.find (fun (id, _) -> id = m) model
                                  with
                                    Not_found ->
                                    print_endline (m ^ " is not found in the model");
                                    raise Not_found
                                in
                                (pred_name, v)
                              ) pred_ms in
           
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
               let newpred = mk_rule goal.var goal.H.args goal.fix f' in
               P.pp_rule newpred |> P.dbg "RULE()";
               Some [newpred]
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
            guessed_unfold_fold transformer goal defs_map f
    else
      begin
        print_endline "Old School Method (Calls other predicate)";
        guessed_unfold_fold transformer goal defs_map f
      end
  end 
;;
(*
let get_removable_indices (rules : H.hes_rule list) =
  
;;

let get_concise_rules rules indices =
  rules
;;

let adjust_call f = f
;;
 *)
let concise (r, f) _ =
  (*
  match r with
    None -> (r, f)
  | Some rules ->
     P.pp_list P.pp_rule rules |> P.dbg "rules";
     P.pp_formula f |> P.dbg "formula";
     let gamma = H.to_typed (rules, env) |> snd in
     
     let r : (Id.Key.t * Type.abstraction_ty) list = IdMap.to_alist gamma in
     let r1 = List.map fst r in
     let r2 = List.map (Id.Key.sexp_of_t) r1 in
     
     (* |> List.map Type.to_simple in *)
     
     (*
     let removable_indices = get_removable_indices rules in
     let rules' = get_concise_rules rules removable_indices in
     let f' = adjust_call f in *)
     (Some rules, f) *)
  (r, f)
;;

let uf = controlled_unfold_fold;;
(* let uf = unfold_fold ;; *)

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
  let ps, args = List.split p_a' in
  let body' = normalize_exists qvs f in
  let goalpred = mk_rule predname ps Fixpoint.Least body' in
  
  let transformer f = f
                      (* |> unfold_formula defs_map *)
           |> normalize_exists qvs
  in
  let r = uf transformer goalpred defs_map f in
  
  let f = U.implode_pred predname args in
  concise (r, f) env

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
       let fs = f' |> cnf_of_formula |> get_conjuncts in (** Optimization Point  *)
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

let rec get_pred_name = function
    H.Var s -> s
  | H.App (f, _) -> get_pred_name f
  | _ -> raise (StrangeSituation "Not a predicate")
;;

let get_pred defs_map f =
  let pred_name = get_pred_name f in
  let pred = try D.find pred_name defs_map with Not_found -> print_endline ("Not found predicate " ^ pred_name); raise Not_found in
  pred;;

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
  let fs = get_conjuncts f in
  let fn x y =
    let dx = get_disjuncts x in
    let dy = get_disjuncts y in
    not (subset dx dy)
  in
  let fs' = reduce fn [] fs in
  let f' = mk_ands fs' in
  P.pp_formula f' |> P.dbg "Reduced conjuncts";
  f'
;;

let reduce_disj f =
  let fs = get_disjuncts f in
  let fn x y =
    let dx = get_conjuncts x in
    let dy = get_conjuncts y in
    not (subset dx dy)
  in
  let fs' = reduce fn [] fs in
  let f' = mk_ors fs' in
  P.pp_formula f' |> P.dbg "Reduced conjuncts";
  f'
;;

let rec unfold_fold_conj goal defs_map f =
  let transformer f = f |> dnf_of_formula |> unsat_elim |> taut_elim |> reduce_disj in
  uf transformer goal defs_map f
;;

let rec unfold_fold_disj goal defs_map f =
  let transformer f = f |> cnf_of_formula |> unsat_elim |> taut_elim |> reduce_conj in
  uf transformer goal defs_map f
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
  P.pp_formula f |> P.dbg "f";
  let fs = get_disjuncts f in
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
       let f = nonatomics |> List.sort_uniq compare_raw_hflz |> mk_ors in
       let newgoalname = new_predicate_name () in
       let args = List.map H.mk_var goal.H.args in
       let ps = goal.H.args in

       let newgoal = {H.var=newgoalname; args=ps; fix=fix; body=f} in
       let r = unfold_fold_disj newgoal defs_map' f in
       let f' = U.implode_pred newgoalname args in
       concise (r, f') env
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
  let fs = get_conjuncts f in
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
       let f = [x; y] |> List.sort_uniq compare_raw_hflz |> mk_ands in
       
       let newgoalname = new_predicate_name () in
       let args = List.map H.mk_var goal.H.args in
       let ps = goal.H.args in

       let newgoal = {H.var=newgoalname; args=ps; fix=fix; body=f} in
       let r = unfold_fold_conj newgoal defs_map' f in
       
       let f' = U.implode_pred newgoalname args in
       concise (r, f') env
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

(*

(r<>0 \/ ((y+z)<>0 \/ z>0)) /\ 
(r<>0 \/ ((y+z)<>0 \/ y>0)) /\ 
(r<>0 \/ ((y+z)<>0 \/ Mult2 x (y-1) (z-1) (r-(2*x)))) /\ 
((y+z)=0 \/ ((y+(z+(-1)))<>0 \/ ((r-x)<>0 \/ z>0))) /\ 
((y+z)=0 \/ ((y+(z+(-1)))<>0 \/ ((r-x)<>0 \/ y>0))) /\ 
((y+z)=0 \/ ((y+(z+(-1)))<>0 \/ ((r-x)<>0 \/ Mult2 x (y-1) (z-1) (r-(2*x))))) /\ 
((y+z)=0 \/ ((y+(z+(-1)))=0 \/ (z>0 \/ DMult x (((y+z)-1)-1) ((r-x)-x)))) /\ 
((y+z)=0 \/ ((y+(z+(-1)))=0 \/ (y>0 \/ DMult x (((y+z)-1)-1) ((r-x)-x)))) /\ 
((y+z)=0 \/ ((y+(z+(-1)))=0 \/ FIXPRED1 x (y+(-1)) (z+(-1)) (r+(0-(2*x)))))

*)
