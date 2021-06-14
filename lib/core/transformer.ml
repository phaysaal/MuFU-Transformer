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

let cnf_of_formula f =
  let rec mk_left x y =
    match y with
    | H.And (a, b) -> H.mk_and (mk_left x a) (mk_left x b)
    | _ -> H.mk_or x y
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
  mk f
;;

let dnf_of_formula f =
  let rec mk_left x y =
    match y with
    | H.Or (a, b) -> H.mk_or (mk_left x a) (mk_left x b)
    | _ -> H.mk_and x y
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
  let f' = mk f in
  P.pp_formula f' |> P.dbg "DNF";
  f'
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

let compare_raw_hflz f1 f2 =
  match f1, f2 with
  | H.Pred _, H.App _ ->
     -1
  | H.App _, H.Pred _ ->
     1
  | _ ->
     H.compare_raw_hflz f1 f2
(* String.compare (H.show_raw_hflz f1) (H.show_raw_hflz f2) *)
;;

let mk fn (f1, f2) =
  if compare_raw_hflz f1 f2 <= 0 then
    fn f1 f2
  else
    fn f2 f1
;;

let rec hflz_to_or_list = function
    H.Or (f1, f2) ->
     let f1' = hflz_to_or_list f1 in
     let f2' = hflz_to_or_list f2 in
     f1' @ f2'
  | f ->
     [cnf_ext f]

and hflz_to_and_list = function
    H.And (f1, f2) ->
      let f1' = hflz_to_and_list f1 in
      let f2' = hflz_to_and_list f2 in
      f1' @ f2'
  | f ->
     [cnf_ext f]
  
and cnf_ext formula =
  match formula with
  (** Equivalence *)
  | H.Or (f1, f2) when equiv f1 f2 ->
     cnf_ext f1
  | H.And (f1, f2) when equiv f1 f2 ->
     cnf_ext f1
  (** Distributivity of | over & *)
  (** (f1 & f2) | f => (f1 | f) & (f2 | f) *)
  | H.Or (H.And (f1, f2), f) ->
     let f' = cnf_ext f in
     mk H.mk_and (mk H.mk_or (cnf_ext f1,f') |> cnf_ext,
            mk H.mk_or (cnf_ext f2,f') |> cnf_ext)
  (** x | (y & z) => (y | x) & (z | x) *)
  | H.Or (f, H.And (f1, f2)) ->
     let f' = cnf_ext f in
     mk H.mk_and (mk H.mk_or (f', cnf_ext f1) |> cnf_ext,
                  mk H.mk_or (f', cnf_ext f2) |> cnf_ext)
  (** Associativity and commutativity *)
  (* | H.Or (f1, f2) ->
     let f1' = cnf_ext f1 in
     let f2' = cnf_ext f2 in
     if f1=f1' && f2=f2' then
       formula
     else
     H.Or (f1', f2') |> cnf_ext *)
  | H.Or _ as f ->
     let fs = hflz_to_or_list f in
     let fs' = List.sort_uniq compare_raw_hflz fs in
     let f' = (mk_ors fs') in
     if f' <> f then
       cnf_ext f'
     else
       f'
  | H.And _ as f ->
     let fs = hflz_to_and_list f in
     let fs' = List.sort_uniq compare_raw_hflz fs in
     let f' = mk_ands fs' in
     if f' <> f then
       cnf_ext f'
     else
       f'
  (** Relational and Arithmetic *)
  | H.Pred (F.Eq, fs) ->
     let fs' = List.sort_uniq compare_raw_hflz fs in
     H.Pred (F.Eq, List.map cnf_ext fs')
  | H.Op (A.Add, fs) ->
     let fs' = List.sort_uniq compare_raw_hflz fs in
     H.Op (A.Add, List.map cnf_ext fs')
  | H.Op (A.Mult, fs) ->
     let fs' = List.sort_uniq compare_raw_hflz fs in
     H.Op (A.Mult, List.map cnf_ext fs')
  | _ -> formula
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
  (* P.pp_formula f |> P.dbg "is_in(0)";
  if f' then P.dbg "is_in" "True" else P.dbg "is_in" "False"; *)
  f'

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
     P.pp_formula f |> P.dbg "f1 \/ f2";
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
  P.pp_formula f' |> P.dbg "EX_dist";
  f'
;;

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
  P.pp_formula f' |> P.dbg "tautology_elimination";
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
  P.pp_formula f' |> P.dbg "unsat_elimination";
  f'
;;

let not_taut_exists s f =
  let t = H.Exists (s, f) in
  not (is_taut t)
;;

let ex_dist2 qvs f =
  let rec aux s = function
    | H.Pred _ as f when is_in s f -> H.Exists (s, f)
    | H.App _ as f when is_in s f -> H.Exists (s, f)
    | H.Or (f1, f2) -> H.Or (aux s f1, aux s f2)
    | H.And _ as f ->
       let fs = cnf_ext f |> hflz_to_and_list in (** Optimization Point  *)
       (* P.pp_list P.pp_formula fs |> P.dbg "fs"; *)
       let is_ins, not_ins = List.partition (is_in s) fs in
       (* P.pp_list P.pp_formula is_ins |> P.dbg "is_ins";
       P.pp_list P.pp_formula not_ins |> P.dbg "not_ins"; *)
       let is_ins' = List.filter (not_taut_exists s) is_ins in
       (* P.pp_list P.pp_formula is_ins' |> P.dbg "is_ins'"; *)
       let is_in' = mk_ands is_ins' in
       let not_in' = mk_ands not_ins in
       if List.length is_ins = 0 then
         is_in'
       else if List.length not_ins = 0 then
         H.Exists (s, is_in')
       else
         H.And (not_in', H.Exists (s, is_in'))
    | f -> f
  in
  let f' = List.fold_left (fun f s ->
               (* s |> P.dbg "s"; *)
               let f' = aux s f in
               (* P.pp_formula f' |> P.dbg "EX_dist(inner)"; *)
               f'
             ) f qvs in (* |> taut_elim in *)
  P.pp_formula f' |> P.dbg "EX_dist";  
  f'
;;


let normalize f =
  f
  |> ex_dist
  |> cnf_ext
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

(*  let rec aux2 = function
      H.And (f1, f2) ->
       aux2 f1 @ aux2 f2
    | H.Or (f1, f2) ->
       aux2 f1 @ aux2 f2
    | f -> [aux [] f]
  in *)
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
      (* print_endline pred.H.var;
      print_endline (H.show_raw_hflz f);
      print_endline "Args:";
      print_endline (P.pp_list P.pp_formula args);
      print_endline "Params:";
      List.iter (fun s -> print_string s; print_string ",") params;
      print_endline "";
      [] *)
      raise ( StrangeSituation "Param-Args mismatch")
  in
  List.fold_left (fun f (to_be, by) ->
      U.subs_var to_be by f
    ) f p_t
;;

let exec_unfold defs_map f =
  let res : (string * H.raw_hflz list) = try explode_pred f with e -> print_endline "exec_unfold"; raise e in

  let f (pred_name, args) =
    let pred = try D.find pred_name defs_map with e -> print_endline pred_name;raise e in
    let params : string list = pred.H.args in
    let temps = get_temps_n (List.length args) in
    let vtemps = List.map (fun t -> H.Var t) temps in
  
    let body' = subs_vars params vtemps pred.H.body in
    let body'' = subs_vars temps args body' in
    body''
  in
  f res
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

let mk_rule n a f b =
    {
    H.var = n;
    args = a;
    fix = f;
    body = b
  }

;;
   
let unfold defs_map goal =
  print_endline ("Original: " ^ (P.pp_formula goal.H.body));
  let body' = unfold_formula defs_map goal.H.body in
  print_endline ("Unfolded: " ^ (P.pp_formula body'));

  let body'' = normalize body' in
  
  print_endline ("Normalized Body: " ^ (P.pp_formula body''));
  body''
;;

let fold goal body =
  P.pp_formula body |> P.dbgn "Before Fold";
  let res, body' = U.find_matching goal.H.var goal.H.args goal.H.body body in
  P.pp_formula body' |> P.dbgn "After Fold";
  res, body'
;;

let add_map map def =
  D.add def.H.var def map
;;

let make_def_map defs =
  List.fold_left add_map D.empty defs 
;;

let rec transform_newgoal defs_map (orig_goal : H.hes_rule) : H.hes_rule =
  let rec aux def_map (goal : H.hes_rule) = function
      0 -> goal
    | n ->
       print_endline "-----------";
       let body' = unfold defs_map goal in
       let res, body'' = fold orig_goal body' in
       let goal' = mk_rule goal.H.var goal.H.args goal.H.fix body'' in
       P.pp_rule goal' |> P.dbg "GOAL'";

       if res then goal' else
       let goal'' = aux def_map goal' (n-1) in
       goal''
  in
  aux defs_map orig_goal 2
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
  let newpreddef = {H.var=newpredname; args=fvs; fix=Fixpoint.Greatest; body=f} in
  (Some newpreddef, newpred)
;;

let rec transform_goal = function
  | H.And _ as f-> make_new_goal f  (* raise (UnsupportedNow "Transform Goal") *)
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
  List.exists (fun a -> let fvs = U.fv a in (* List.mem s fvs *) fvs = [s] || List.length fvs = 0) args
;;

let reduce_args qvs args =
  List.filter (fun (_, a) -> let fvs = U.fv a in (* not (List.mem sv fvs) *) List.for_all (fun sv -> fvs <> [sv]) qvs && List.length fvs > 0) args
;;

let reduce_args1 sv args =
  List.filter (fun  a -> let fvs = U.fv a in (* not (List.mem sv fvs)  *) fvs <> [sv] && List.length fvs > 0) args
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

let normalize_exists qvs f =
  P.pp_list P.id qvs |> P.dbg "QVs";
  let f' = f
           |> dnf_of_formula
           (* |> H.mk_exists s *)
           |> ex_dist2 qvs
           |> taut_elim
         |> unsat_elim
  in
  P.pp_formula f' |> P.dbg "Normalized";
  f'
;;
  
let step2 qvs f defs_map p_a fixpoint predname =
  P.pp_formula f |> P.dbgn "f";
  let fvs = fv f in
  let p_a' = reduce_args qvs p_a in
  let p_a' = List.filter (fun (p,_) -> List.for_all (fun s -> p<>s) qvs && List.mem p fvs) p_a' in
  let f' = f
           |> unfold_formula defs_map
           |> normalize_exists qvs
           (* |> reverse_subs p_a' *)
  in
  let ps, args = List.split p_a' in
  (* P.pp_list P.id ps |> P.dbg "Original Params"; *)
  
  let body' = normalize_exists qvs f (* List.fold_left (fun f s -> H.Exists (s,f)) f qvs *) in
   
  let goalpred = {H.var=predname; args=ps; fix=fixpoint; body=body'} in

  (* P.pp_rule goalpred |> P.dbgn "Goal Pred"; *)
  let _, body = fold goalpred f' in
  let f = U.implode_pred predname args in
  let newpred = {H.var=predname; args=ps; fix=fixpoint; body=body} in
  (* P.pp_formula f |> P.dbgn "f";
  P.pp_rule newpred |> P.dbgn "New Pred"; *)
  
  Some [newpred], f
  (*
  (* let newpredname = new_predicate_name () in *)

  let k = List.length p_a' in
  let params = new_params k in
  P.pp_list P.id params |> P.dbg "New Params";
   
  let params' = List.map H.mk_var params in
  let f'' = subs_vars ps params' f' in
  P.pp_formula f'' |> P.dbgn "f''";
  
  let f''' = ex_trans_formula s predname newpredname f'' in
  P.pp_formula f''' |> P.dbgn "f'''";
  

  
  P.pp_formula f' |> P.dbgn "Before fold in step2";
  P.pp_formula (H.Exists (s,f)) |> P.dbgn "body";
  
  P.pp_formula body |> P.dbgn "After fold in step2";
  if is_folded then
    let newpred = {H.var=newpredname; args=params; fix=fixpoint; body=body} in
    (Some [newpred], f)
  else
    begin
      let newpred = {H.var=newpredname; args=params; fix=fixpoint; body=f'''} in
      P.pp_rule newpred |> P.dbgn "New Pred";
      let f = U.implode_pred newpredname a_s in 
      P.pp_formula f |> P.dbgn "f";
      (Some [newpred], f)
    end
   *)
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
       print_endline "----------";
       print_endline x;
       a |> P.pp_formula |> P.dbg "a";
       b |> P.pp_formula |> P.dbg "b";
       let (c1,d1) = AP.cx_d x a in
       let (c2,d2) = AP.cx_d x b in

       P.dbg "c1" (P.pp_list AP.pp_pairs c1);
       P.dbg "c2" (P.pp_list AP.pp_pairs c2);
       P.dbg "d1" (P.pp_list AP.pp_pairs d1);
       P.dbg "d2" (P.pp_list AP.pp_pairs d2);
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
              c1 |> AP.pp_pairss |> P.dbg "c1";
              H.Op (Arith.Div, [H.Op (Arith.Sub, [AP.list_to_exp d2; AP.list_to_exp d1]); AP.list_to_exp c1])
            | _ ->
               (** x*c1+d1 = x*c2+d2 ==> x = (d2-d1)/(c1-c2)  *)
               c1 |> AP.pp_pairss |> P.dbg "c1";
               H.Op (Arith.Div, [H.Op (Arith.Sub, [AP.list_to_exp d2; AP.list_to_exp d1]); H.Op (Arith.Sub, [AP.list_to_exp c1; AP.list_to_exp c2])])
       in
       P.pp_formula r |> P.dbg "r";
       let r' = AP.normalize r in
       P.pp_formula r |> P.dbg "r'";
       r'
       
     end
  | _ -> raise (UnsupportedNow "get_value")
;;

let combine_res = List.hd
;;


let rec dist_exists s = function
    H.And (f1, f2) -> H.And (dist_exists s f1, dist_exists s f2)
  | H.Or (f1, f2) -> H.Or (dist_exists s f1, dist_exists s f2)
  | f -> H.Exists (s, f)
;;
  
(** SINGLE CONSTRAINT *)
let rec find_constraint x f =
  let conjs = conj_to_list f in
  (* print_int (List.length conjs); print_endline " CONJS"; *)
  let constraints, nonconstraints = List.partition (function H.Pred _ as c -> List.mem x (U.fv c) | _ -> false) conjs in
  (* print_int (List.length constraints); print_endline " CONSTRAINTS"; *)
  let vals = List.map (get_value x) constraints in
  if List.length constraints = 0 then
    f, false
  else
    begin
      let value = combine_res vals in
      (* P.pp_formula value |> P.dbg "value"; *)
      let nonconstraints' = List.map (U.subs_var x value) nonconstraints in
      list_to_and nonconstraints', List.length nonconstraints' <> List.length conjs
    end
;;

(**
FIXV3 x y z r = (z = 0 \/ FIXV3 x y (z - 1) (r - 1))

(FIXV2 x y z r) = ((z = 0) /\ (z + r - y) = x ) \/ ((z <> 0) /\ (FIXV2 x y (z - 1) (r - 1))) 

*)
let rec is_atomic = function
    H.Pred _ -> true
  | H.And _ -> false
  | H.Or _ -> false
  | H.App _ -> true
  | H.Exists _ -> true
  | _ -> true
;;

let predicate_for_exists goal =
    (*H.App _ as f ->
     let predname, args = explode_pred f in
     let pred = D.find predname defs_map in
     let fixpoint = pred.H.fix in
     let p_a = List.combine pred.H.args args in
     predname, p_a, args, fixpoint
  | _ -> *)
     let newgoalname = new_predicate_name () in
     let args = List.map H.mk_var goal.H.args in
     let p_a = List.combine goal.H.args args in
     newgoalname, p_a, args, goal.H.fix
;;

let exec_exists_elim goal defs_map qvs f =
  print_endline "====================";
  P.pp_formula f |> P.dbgn "Original";

  let (f',qvs') = List.fold_left (fun (f, qvs') qv ->
                       let f', b = find_constraint qv f in
                       if b then
                         (f', qvs')
                       else
                         (f, qv::qvs')
                     ) (f,[]) qvs in

  let qvs'' = List.filter (fun qv -> is_in qv f') qvs' in
  
  let predname, p_a, _, fixpoint = predicate_for_exists goal  (* explode_pred f *) in
  step2 qvs'' f' defs_map p_a fixpoint predname
           
  (* match f with
    H.Exists (s, f) ->
     begin
       let f', _ = find_constraint s f in
       P.pp_formula f' |> P.dbg ("After using constraint ");
       if not (is_in s f') then
         (None, f')
       else
         begin
           let predname, p_a, _, fixpoint = predicate_for_exists goal  (* explode_pred f *) in
           let sv = H.mk_var s in
       
       (* if not (is_candidate s args) then
         (None, f)
       else *)
           step2 s f' defs_map p_a fixpoint predname
         end
     end
  | _ ->
     raise ( StrangeSituation "RRRRRRR") *)
;;

let rec has_constraint = function
    H.Pred _ -> true
  | H.And (f1, f2) -> has_constraint f1 || has_constraint f2
  | H.Or (f1, f2) -> has_constraint f1 || has_constraint f2
  | _ -> false
;;

(*
let elim_exists_using_constraint f =
  let rec aux s = function
      H.Exists (s1, f1) -> 
      let f1' = aux s1 f1 in
      let f1'', b = find_constraint s f1' in
      if b then
        f1''
      else
        f1'
    | f -> f
  in

  match f with
    H.Exists (s, f1) ->
    aux s f1
  | _ -> f
;;
 *)
(*
let exists_elim3 defs_map f =
  let f1 = elim_exists_using_constraint f in
  P.pp_formula f1 |> P.dbgn "After constraint usage";
  
;;
 *)
(*
let exists_elim2 goal defs_map f =
  (* Make new goal *)
  let newbody = exists_elim3 defs_map f in
  let newgoalname = new_predicate_name () in
  let newgoal = {H.var=newgoalname; H.args=goal.H.args; H.fix=goal.H.fix; H.body=newbody} in
  let newgoalexp = List.map H.mk_var goal.H.args |> U.implode_pred newgoalname in
  Some [newgoal], newgoalexp
;;
 *)
    (* exec_exists_elim defs_map s = function
    H.App _ as f ->
     let predname, args = explode_pred f in
     let sv = H.mk_var s in
     let pred = D.find predname defs_map in
     let fixpoint = pred.H.fix in
     let p_a = List.combine pred.H.args args in
     let (r, f') =
       if not (is_candidate s args) then
         (None, f)
       else
         step2 s f defs_map p_a fixpoint predname
     in
     P.pp_formula f  |> P.dbg "exec_exists_elim App f ********";
     P.pp_formula f' |> P.dbg "exec_exists_elim App f' ********";
     (r, f')
  | H.Or _ ->
     raise (UnsupportedNow "Exsits Elim (or)")
  | H.And _ as f ->
     P.pp_formula f |> P.dbg ("AND ..");
     let f', b = find_constraint s f in
     let (r, f') =
       if b then
         (None, f')
       else
         begin
           let f'' = dist_exists s f in
           P.pp_formula f''  |> P.dbg "exec_exists_elim And(Dist) f'' ********";
           f'' |> exists_elim defs_map
         end
     in
     P.pp_formula f  |> P.dbg "exec_exists_elim And f ********";
     P.pp_formula f' |> P.dbg "exec_exists_elim And f' ********";
     (r, f')
  | H.Exists (s1, f) ->
     begin
       P.pp_formula f |> P.dbg ("EXISTS .." ^ s1);
       let (r1, f') = exec_exists_elim defs_map s1 f in
       P.pp_formula f  |> P.dbg "exec_exists_elim Exists f *";
       P.pp_formula f' |> P.dbg "exec_exists_elim Exists f' *";
       let (r2, f'') = exec_exists_elim defs_map s f' in

       P.pp_formula f  |> P.dbg "exec_exists_elim Exists f *";
       P.pp_formula f'' |> P.dbg "exec_exists_elim Exists f'' *";
       let (r, f') = concat_option r1 r2, f'' in
(*         match r1, r2 with
           None, _ -> r2, f''
         | _, None -> r1, f''
         | Some xs, Some ys -> Some (xs@ys), f''
       in *)
       P.pp_formula f  |> P.dbg "exec_exists_elim Exists f ********";
       P.pp_formula f' |> P.dbg "exec_exists_elim Exists f' ********";
       (r, f')
     end
  | _ -> raise (UnsupportedNow "Exsits Elim (else)")
       
and *)

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

let rec exists_elim goal defs_map f =
  match f with
    H.Or (f1, f2) ->
     P.pp_formula f |> P.dbg "OR";
     let (res1, f1') = exists_elim goal defs_map f1 in
     let (res2, f2') = exists_elim goal defs_map f2 in
     let res = concat_option res1 res2 in
     (res, H.Or (f1',f2'))
  | H.And (f1, f2) ->
     P.pp_formula f |> P.dbg "AND";
    let (res1, f1') = exists_elim goal defs_map f1 in
    let (res2, f2') = exists_elim goal defs_map f2 in
    let res = concat_option res1 res2 in
    (res, H.And (f1',f2'))
  | H.Exists _ as f ->
     begin
       let (qvs, f1') = get_qvs_and_body f in
       let (res2, f') = exec_exists_elim goal defs_map qvs f1' in
       (* P.pp_formula f' |> P.dbg ("After eliminating " ^ s); *)
       (* concat_option res1 *) res2, f'
     end
  | _ -> (None, f)
;;

    
let transform_hes (defs : H.hes) goal =
  let defs_map = make_def_map defs in (** List to Map.Make *)
  P.pp_formula goal.H.body |> P.dbg "Goal";
  let (res, goal') : (H.hes option * H.raw_hflz) =
    goal.H.body
    |> dnf_of_formula
    |> exists_elim goal defs_map
    |> snd_apply normalize
  in
  P.pp_formula goal' |> P.dbg "New Goal";
  let newgoal_o, origbody = transform_goal goal' in
  P.pp_formula origbody |> P.dbg "Origbody";
  match newgoal_o with
    None ->
     begin
       print_endline "None";
      let goaldef : H.hes_rule = {H.var=goal.H.var; args=goal.H.args; fix=Fixpoint.Greatest; body=goal'} in
      match res with
        None ->
         transform_newgoal defs_map goaldef :: defs
      | Some newgoals ->
         let defs_map' = List.fold_left (fun dm g -> D.add g.H.var g dm) defs_map newgoals in
         P.pp_rule goaldef |> P.dbgn "Transformed Goal";
         P.pp_list ~sep:"\n" P.pp_rule newgoals |> P.dbgn "New Goals";
         transform_newgoal defs_map' goaldef :: newgoals @ defs
    end
  | Some newpreddef ->
     begin
       print_endline "Some";
       let goaldef : H.hes_rule = {H.var=goal.H.var; args=goal.H.args; fix=Fixpoint.Greatest; body=origbody} in
       let extra_defs = 
         match res with
           None -> []
         | Some newdefs ->
            newdefs
       in
       let defs_map' = List.fold_left (fun dm g -> D.add g.H.var g dm) defs_map extra_defs
                     |> D.add newpreddef.H.var newpreddef in
       
       P.pp_rule newpreddef |> P.dbgn "Transformed Goal";
       (* P.pp_list ~sep:"\n" P.pp_rule newgoals |> P.dbgn "New Goals"; *)
       goaldef:: transform_newgoal defs_map' newpreddef :: extra_defs @ defs
     end
;;
  
    
(**
   Original Algorithm

   find_body_and_fold body iters
   ------------------------------
   body = expandExists body   // if the pattern is ∃x.A o B then make is ∃x.A o ∃x.B
   body = simplifyExists body
   body = expandConjSubexpr body
   disj = getDisj body
   for all it in disj
       e = fold_conj it iters
       disj2 = add e to disj2
   for all it in disj2
       if isOpX<FAPP> then
          add it to constr
          remove it from disj2
   if size of disj2  < 2 then
       for all it in disj2
          add it to constr
       return disjoin constr efac
   else
       flaOrig = disjoin constr efac
       filter fla isConst inserter(freevars, freevars.begin())
       fvar = new_fvar freevars
       flaRel = fapp fvar freevars
       ...
       
   return disjoin constr efac
   --------------------------------

   expandExists body
   --------------------------------
   dagVisit rw(new ExpandExists) exp
   --------------------------------
 *)

(**
  visit (expr, cache)
  -------------
  if expr->useCount > 1
     cit = cache.find expr
     if cit is not cache.end then return cit->second
  end  
  va = v (expr)
  if va.isSkipKids
     res = expr
  else if va.isChangeTo 
     res = va.getExpr
  else
     res = va.isChangeDoKidsRewrite ? va.getExpr : expr
     if res->arity > 0
        

  QFregularizer
  --------------
  




  regularizeQF (exp)
  ----------------------
  map :: Expr -> ExprVector
  vars = getQVars exp
  for all a in vars
      sub = replaceAll (a.first, replaced)
      rw = new RQ<QFregularizer> with a->second
      b = dagVisit (rw, sub)
      replaced[a->first] = b
      exp = replaceAll exp sub b
  end for
  return exp

  initialize
  --------------
  for all conjunct c:
      if c has form FORALL 
         c = regularizeQF(c)
         if c->last has form FAPP
            flaMain = c
            flaRel = c->last
         else if c->last has form EQ: ∃s.Q
            flaForAll = c
            fla = c->last
            fixVars += s
            nonRecDef[c->last->first] = Q
            recDefsBinders[s] = c
         end
     end
     if c has form AND and c->right has form FORALL and c->right->last has form EQ
        var = c->left
        pref = var
        c = regularizeQF (c->right)
        if pref="mu" then
           def = c->last->right
           for all a in recDefsNu
               if def contains a->first->left
                  error
               end
           end for
           recDefsMu[c->last->left] = def
           recDefsBinders[c->last->left] = c
           fixVars += c->last->left
           muVar = var
        else if pref = "nu" then
           def = c->last->right
           for all a in recDefsMu
               if def contains a->first->left
                  error
               end
           end for
           recDefsNu[c->last->left] = def
           recDefsBinders[c->last->left] = c
           fixVars += c->last->left
           muVar = var
        end
     end
   end for
   usedNu = false
   flaOrig = fla
   fla = fla->right
 *)
