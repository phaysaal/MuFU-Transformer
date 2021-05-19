open Hflmc2_syntax
   
module H = Raw_hflz
module F = Formula
module A = Arith

module P = Printer

module D = Map.Make(String)

exception StrangeSituation of string
                       
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

let subs_var to_be by f =
  let rec select_from_two fn f f1 f2 =
     let f1', b1 = aux f1 in
     let f2', b2 = aux f2 in
     if b1 && b2 then
       fn f1' f2', true
     else if b1 then
       fn f1' f2, true
     else if b2 then
       fn f1 f2', true
     else
       f, false

  and select_from_one fn f f1 =
     let f1', b1 = aux f1 in
     if b1 then
       fn f1', true
     else
       f, false

  and select_from_list fn f fs =
    let (fs', b) = List.fold_left (fun (fs_acc, b_acc) f ->
                       let (f', b) = aux f in
                       if b then
                         f'::fs_acc, true
                       else
                         f::fs_acc, b_acc
                     ) ([], false) (List.rev fs) in
    if b then
      fn fs', true
    else
      f, false
    
  and aux = function
  | H.Bool _ as f -> f, false
  | H.Var x when x = to_be -> by, true
  | H.Var _ as f -> f, false 
  | H.Or (f1, f2) as f ->
     select_from_two (fun f1 f2 -> H.mk_or f1 f2) f f1 f2
  | H.And (f1, f2) as f ->
     select_from_two (fun f1 f2 -> H.mk_and f1 f2) f f1 f2
  | H.Abs (s, f1) as f ->
     select_from_one (fun f' -> H.mk_abs s f') f f1
  | H.App (f1, f2) as f ->
     select_from_two (fun f1 f2 -> H.mk_app f1 f2) f f1 f2
  | H.Int _ as f -> f, false
  | H.Op (o, f1) as f ->
     select_from_list (fun f' -> H.mk_op o f') f f1
  | H.Pred (p, f1) as f ->
     select_from_list (fun f' -> H.mk_preds p f') f f1
  | H.Forall (s, f1) as f ->
     select_from_one (fun f' -> H.mk_forall s f') f f1
  | H.Exists (s, f1) as f ->
     select_from_one (fun f' -> H.mk_exists s f') f f1
  in
  aux f |> fst
     

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
     H.And (H.Or (cnf_ext f1,f') |> cnf_ext,
            H.Or (cnf_ext f2,f') |> cnf_ext)
  (** x | (y & z) => (y | x) & (z | x) *)
  | H.Or (f, H.And (f1, f2)) ->
     let f' = cnf_ext f in
     H.And (H.Or (f', cnf_ext f1) |> cnf_ext,
            H.Or (f', cnf_ext f2) |> cnf_ext)
  (** Associativity and commutativity *)
  | H.Or _ as f ->
     let fs = hflz_to_or_list f in
     let fs' = List.sort_uniq compare_raw_hflz fs in
     mk_ors fs'
  | H.And _ as f ->
     let fs = hflz_to_and_list f in
    let fs' = List.sort_uniq compare_raw_hflz fs in
    mk_ands fs'
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

let rec does_have x f =
  match f with
  | H.Bool _ -> false
  | H.Var _ -> false
  | H.Or (f1, f2) ->
     does_have x f1 || does_have x f2
  | H.And (f1, f2) ->
     does_have x f1 || does_have x f2
  | H.Abs (_, f1) ->
     does_have x f1
  | H.App (f1, f2) ->
     does_have x f1 || does_have x f2
  | H.Int _ -> false
  | H.Op (_, f1) ->
     List.exists (fun f -> does_have x f) f1
  | H.Pred (_, _) ->
     if f = x then
       true
     else
       false
  | H.Exists (_, _) ->
     false
  | H.Forall (_, _) ->
     false

let rec is_taut f =
  match f with
    H.Or (H.Pred (Formula.Eq, [a;b]), f2) ->
     if does_have  (H.Pred (Formula.Neq, [a;b])) f2 ||
          does_have  (H.Pred (Formula.Neq, [b;a])) f2 then
       true
     else
       is_taut f2
  | H.Or (f1, f2) ->
     is_taut f1 || is_taut f2
  | _ -> false
(** CALL z3 *)
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
     if is_taut f1' then
       f2'
     else if is_taut f2' then
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



(*
  (x & y) & (z & w) 
= (x & (y & (z & w)))

  (x1 & x3) & (x4 & x2)
= 
 *)
let build_args f =
  let rec aux acc = function
      H.App (f1, f2) ->
       aux (f2::acc) f1
    | H.Var s -> s, acc
    | _ -> raise (StrangeSituation "Unsupported Predicate Naming")
  in
  aux [] f
;;

let rec get_temps_n n =
  if n > 0 then
    ("##~~@@" ^ (string_of_int n)) ::get_temps_n (n-1)
  else
    []
;;

let exec_unfold defs_map f =
  let (pred_name, args) : string * H.raw_hflz list = build_args f in
  let pred = D.find pred_name defs_map in
  let params : string list = pred.H.args in
  let temps = get_temps_n (List.length args) in
  let vtemps = List.map (fun t -> H.Var t) temps in
  
      
  let p_t =
    try
      List.combine params vtemps
    with
      _ ->
      print_endline pred.H.var;
      print_endline (H.show_raw_hflz f);
      print_endline "Args:";
      print_endline (P.pp_list P.pp_formula args);
      print_endline "Params:";
      List.iter (fun s -> print_string s; print_string ",") params;
      print_endline "";
      []
  in
  let t_a = List.combine temps args in
  let body' = List.fold_left (fun f (to_be, by) ->
                  subs_var to_be by f
                ) pred.H.body p_t in
  let body'' = List.fold_left (fun f (to_be, by) ->
                  subs_var to_be by f
                ) body' t_a in
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
  (* | H.App (H.Var pred_name, f2) -> *)
  | H.App (_, _) ->
     exec_unfold defs_map f
  (*     H.mk_app (unfold_formula defs_map f1) (unfold_formula defs_map f2) *)
  | H.Int _ -> f
  | H.Op (o, f1) ->
     H.mk_op o (List.map (unfold_formula defs_map ) f1)
  | H.Pred (p, f1) ->
     H.Pred (p, List.map (unfold_formula defs_map ) f1)
  | H.Exists (s, f1) ->
     H.Exists (s, unfold_formula defs_map  f1)
  | H.Forall (s, f1) ->
     H.Forall (s, unfold_formula defs_map f1)
         
let unfold defs_map goal =
  print_endline ("Original: " ^ (P.pp_formula goal.H.body));
  let body' = unfold_formula defs_map goal.H.body in
  print_endline ("Unfolded: " ^ (P.pp_formula body'));
  let body'' = normalize body' in
  print_endline ("Normalized: " ^ (P.pp_formula body''));

  {
    H.var = goal.H.var;
    args = goal.H.args;
    fix = goal.H.fix;
    body = body'
  }
;;

let fold hes = hes;;

let add_map map def =
  D.add def.H.var def map
;;

let make_def_map defs =
  List.fold_left add_map D.empty defs 
;;

let rec transform_hes defs (goal : H.hes_rule) =
  let defs_map = make_def_map defs in
  let rec aux def_map (goal : H.hes_rule) = function
      0 -> goal
    | n ->
       print_endline "-----------";
       let goal' = unfold defs_map goal in
       let goal'' = fold goal' in
       aux def_map goal'' (n-1)
  in
  aux defs_map goal 1
;;
  
  

    
