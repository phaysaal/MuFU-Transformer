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
  mk f
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

let build_exists s f =
  if is_in s f then
    H.Exists (s, f)
  else
    f
;;

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
;;

let is_taut f =
  Z.is_tautology f
;;

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
  let (pred_name, args) : string * H.raw_hflz list = try explode_pred f with e -> print_endline "exec_unfold"; raise e in
  let pred = try D.find pred_name defs_map with e -> print_endline pred_name;raise e in
  let params : string list = pred.H.args in
  let temps = get_temps_n (List.length args) in
  let vtemps = List.map (fun t -> H.Var t) temps in
  
  let body' = subs_vars params vtemps pred.H.body in
  let body'' = subs_vars temps args body' in
  body''
;;


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
  | H.And _ -> raise (UnsupportedNow "Transfer Goal")
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

let reduce_args sv args =
  List.filter (fun (_, a) -> let fvs = U.fv a in fvs <> [sv] && List.length fvs > 0) args
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
  List.fold_left (fun f (to_be, by) ->
      U.subs_f to_be by f
    ) f a_p
;;

let step2 s f defs_map p_a fixpoint predname =
  P.pp_formula f |> P.dbgn "f";
  let p_a' = reduce_args s p_a in
  let f' = f
           |> unfold_formula defs_map
           |> dnf_of_formula
           |> H.mk_exists s
           |> ex_dist
           |> taut_elim
           |> reverse_subs p_a'
  in
  P.pp_formula f' |> P.dbgn "After Unfold";

  let newpredname = new_predicate_name () in
  
  let k = List.length p_a' in
  let params = new_params k in
  P.pp_list P.id params |> P.dbg "New Params";
  let ps, a_s = List.split p_a' in
  P.pp_list P.id ps |> P.dbg "Original Params";
  let params' = List.map H.mk_var params in
  let f'' = subs_vars ps params' f' in
  P.pp_formula f'' |> P.dbgn "f''";
  
  let f''' = ex_trans_formula s predname newpredname f'' in
  P.pp_formula f''' |> P.dbgn "f'''";
  
  let newpred = {H.var=newpredname; args=params; fix=fixpoint; body=f'''} in
  P.pp_rule newpred |> P.dbgn "New Pred";

  let f = U.implode_pred newpredname a_s in 
  P.pp_formula f |> P.dbgn "f";
  
  (Some [newpred], f)

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
       let r =
         match c1 with
           [] ->
            (** d1 = x*c2+d2 ==> x = (d1-d2)/c2  *)
            print_endline "@1";
            H.Op (Arith.Div, [H.Op (Arith.Sub, [AP.list_to_exp d1; AP.list_to_exp d2]); AP.list_to_exp c2])
         | _ ->
            match c2 with
              [] ->
              (** x*c1+d1 = d2 ==> x = (d2-d1)/c1  *)
              print_endline "@2";
              c1 |> AP.pp_pairss |> P.dbg "c1";
              H.Op (Arith.Div, [H.Op (Arith.Sub, [AP.list_to_exp d2; AP.list_to_exp d1]); AP.list_to_exp c1])
            | _ ->
               (** x*c1+d1 = x*c2+d2 ==> x = (d2-d1)/(c1-c2)  *)
              print_endline "@3";
              c1 |> AP.pp_pairss |> P.dbg "c1";
              H.Op (Arith.Div, [H.Op (Arith.Sub, [AP.list_to_exp d2; AP.list_to_exp d1]); H.Op (Arith.Sub, [AP.list_to_exp c1; AP.list_to_exp c2])])
       in
       P.pp_formula r |> P.dbg "r";
       let r = AP.normalize r in
       print_endline "###";
       r
       
     end
  | _ -> raise (UnsupportedNow "get_value")
;;

let combine_res = List.hd
;;

(** SINGLE CONSTRAINT *)
let rec find_constraint x f =
  let conjs = conj_to_list f in
  print_int (List.length conjs); print_endline "";
  let constraints, nonconstraints = List.partition (function H.Pred _ as c -> List.mem x (U.fv c) | _ -> false) conjs in
  print_int (List.length constraints); print_endline "";
  let vals = List.map (get_value x) constraints in
  let value = combine_res vals in
  P.pp_formula value |> P.dbg "value";
  let nonconstraints' = List.map (U.subs_var x value) nonconstraints in
  list_to_and nonconstraints', List.length nonconstraints' <> List.length conjs
;;

(**
FIXV3 x y z r = (z = 0 \/ FIXV3 x y (z - 1) (r - 1))

(FIXV2 x y z r) = ((z = 0) /\ (z + r - y) = x ) \/ ((z <> 0) /\ (FIXV2 x y (z - 1) (r - 1))) 

*)

let exec_exists_elim defs_map f =
  print_endline "====================";
  P.pp_formula f |> P.dbgn "Original";

  let rec aux f =
    match f with
      H.Exists (s, f) ->
       begin
         let f', b = find_constraint s f in
         if b then
           (s, f', "", [], true)
         else
           let predname, args = explode_pred f in
           (s, f, predname, args, false)
       end
    | _ ->
       raise ( StrangeSituation "RRRRRRR")
  in
  let (_s, _f, _X, _args, b) = aux f in
  print_endline "DDD@@";
  if b then
    begin
      
      (None, _f)
    end
  else
    begin
      let _sv = H.mk_var _s in
      print_endline "DDD";
      let pred = D.find _X defs_map in
      print_endline "DDD";
      let fixpoint = pred.H.fix in
      let p_a = List.combine pred.H.args _args in
      
      if not (is_candidate _s _args) then
        (None, f)
      else
        step2 _s _f defs_map p_a fixpoint _X
    end
;;

let rec exists_elim defs_map f =
  match f with
    H.Or (f1, f2) ->
    let (res1, f1') = exists_elim defs_map f1 in
    let (res2, f2') = exists_elim defs_map f2 in
    let res = concat_option res1 res2 in
    (res, H.Or (f1',f2'))
  | H.And (f1, f2) ->
    let (res1, f1') = exists_elim defs_map f1 in
    let (res2, f2') = exists_elim defs_map f2 in
    let res = concat_option res1 res2 in
    (res, H.And (f1',f2'))
  | H.Exists (s,f1) as f ->
     begin
       print_endline ("EXISTS " ^ s);
       let (op_res1, f1') = exists_elim defs_map f1 in
       let (op_res2, f') = exec_exists_elim defs_map (H.Exists (s,f1')) in
       match op_res1, op_res2 with
         None, _ -> op_res2, f'
       | _, None -> op_res1, f'
       | Some xs, Some ys -> Some (xs@ys), f'
     end
  | _ -> (None, f)
;;

    
let transform_hes (defs : H.hes) goal =
  let defs_map = make_def_map defs in
  let (res, goal') : (H.hes option * H.raw_hflz) =
    goal.H.body
    |> dnf_of_formula
    |> exists_elim defs_map
    |> snd_apply normalize
  in
  
  let newgoal_o, origbody = transform_goal goal' in
  match newgoal_o with
    None ->
    begin
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
   body = expandExists body
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
