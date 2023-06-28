open Hflmc2_syntax
   
module H = Raw_hflz
(* module T = Transformer *)
module P = Printer
module S = Set.Make(Int)
module U = MatchMaker
module L = Tools
module AP = ArithmeticProcessor
module D = Map.Make(String)
module RH = Regex_handler
module Z = Z3Interface
module C = UFCommon
         
let _or = 0
let _and = 1

let count = ref 0
          
exception Strange of string

type formula = FAnd of formula list
             | FOr  of formula list
             | FExists of string * formula
             | FAtom of H.raw_hflz

let rec list_of_conj = function
    H.And (a,b) -> list_of_conj a @ list_of_conj b
  | f -> [f]
;;

let rec list_of_disj = function
    H.Or (a,b) -> list_of_disj a @ list_of_disj b
  | f -> [f]
;;

let list_to_conj = function
    [] -> failwith "No conjunct"
  | x::xs ->
     List.fold_left H.mk_and x xs
;;

let list_to_disj = function
    [] -> failwith "No disjunct"
  | x::xs ->
     List.fold_left H.mk_or x xs

let rec raw_to_formula = function
    H.And (a, b) ->
     let la = list_of_conj a |> List.map raw_to_formula in
     let lb = list_of_conj b |> List.map raw_to_formula in
     FAnd (la@lb)
  | H.Or (a, b) ->
     let la = list_of_disj a |> List.map raw_to_formula in
     let lb = list_of_disj b |> List.map raw_to_formula in
     FOr (la@lb)
  | H.Exists (xs, a) ->
     FExists (xs, raw_to_formula a)
  | f -> FAtom f
;;

let rec formula_to_raw = function
    FAnd la ->
     list_to_conj @@ List.map formula_to_raw la
  | FOr la ->
     list_to_disj @@ List.map formula_to_raw la
  | FExists (s, a) ->
     H.mk_exists s @@ formula_to_raw a
  | FAtom a -> a
;;

(*
let rec nf connective_of_goal formula =
  if connective_of_goal = L._and then
    C.dnf_of_formula formula
  else if connective_of_goal = L._or then
    C.cnf_of_formula formula
  else if connective_of_goal = L._exists then
    nf_of_exists connective_of_goal formula
  else
    formula

and nf_of_exists connective_of_goal = function
    H.Exists (s, a) -> H.Exists (s, nf_of_exists connective_of_goal a)
  | f -> nf connective_of_goal f 
;;
*)
    
let print_size_change_graph graph =
  let print_edge v = (fun (xx,l) ->
      Printf.printf "edge: %s ->" v;
      List.iter (fun (x, w, y) ->
          Printf.printf "(%s,%s,%s) " (x) (string_of_int w) ( y)
        ) l;
      Printf.printf "->%s\n" xx
    )
  in
  let print_graph v edges =
    P.dbg "Predicate" v;
    List.iter (print_edge v) edges
  in
  D.iter print_graph graph;;

let get_size_change_graph defs_map =
    let aux params i predcall =
      let (pred, args) = U.explode_pred predcall in
      let pars = (D.find pred defs_map).H.args |> List.map H.mk_var in
      let p_a = try List.combine pars args
                with e -> P.pp_list P.pp_formula pars |> P.dbg "pars";
                          P.pp_list P.pp_formula args |> P.dbg "args";
                          raise e in
      let get_edges acc p =
        let p' = H.mk_var p in
        List.fold_left
          (fun acc (p, a) ->
            let r = H.Op (Arith.Sub, [a;p']) |> AP.normalize in
            if L.is_const r then
              (p', L.get_int r, p)::acc
            else
              acc
          ) acc p_a in 
      let edges = List.fold_left get_edges [] params in
      ((pred, i), edges)
  in
  let f v =
    let name = v.H.var in
    let params = v.H.args in
    let body = v.H.body in
    let predcalls = L.get_predicates body in
    List.mapi (aux params) predcalls 
  in
  D.map f defs_map
;;

let get_reduced_gnfa gnfas x y =
    let gnfa = D.find x gnfas in
    let reduced_gnfa = RH.reduce gnfa y in
    let r_gnfa = D.find y reduced_gnfa in
    r_gnfa
;;

let mk_reg_ex gnfas dest src =
    let x = U.explode_pred src |> fst in
    let y = U.explode_pred dest |> fst in
    let regex = get_reduced_gnfa gnfas x y in
    regex
;;

let mk_constrained_regex regex =
    let m = RH.R.newvar () in
    let regex' = RH.R.simplify_alter regex in (** alter list to alter tuple *)
    let cons_regex, constraints , bookmarks = regex' |> RH.R.straight m [] in
    let constraints' = RH.R.mk_and constraints (RH.R.eq m RH.R.one) in
    cons_regex, constraints', (regex', m, bookmarks)
;;

let rec to_prime = function
    H.Var s -> H.Var (s ^ "'")
  | H.Int _ as i -> i
  | H.Op (op, xs) -> H.Op (op, List.map to_prime xs)
  | x -> x

let subs_edge _ y (_, f, _) g =
  (* let a' = if x = a then y else a in
  let b' = if x = b then y else a in
  (a', f, b') *)
  let v = to_prime g in
  (v, RH.R.add y f)

  
let mk_subs_summary defs_map pr_goals src summary =
  let matching_args xs ys =
    (List.map U.fv xs |> List.concat |> List.sort String.compare) = (List.map U.fv ys |> List.concat |> List.sort String.compare)
  in
  let (pred, args) = U.explode_pred src in
  let (_, gl_args) = List.map U.explode_pred pr_goals |> List.find (fun (a,args') -> a=pred && matching_args args args') in
  let params = (D.find pred defs_map).H.args in
  let rec aux ps rs ss gl_args =
    match ps, rs, ss, gl_args with
      [], [], [], [] -> []
    | p::ps', r::rs', s::ss', g::gs ->
       subs_edge p r s g::aux ps' rs' ss' gs
    | _ -> raise (Strange "Param, Arg, Summary dimension does not match")
  in
  aux params args summary gl_args
;;

let mk_eq a b =
  H.Pred (Formula.Eq, [a; b])
;;

let mk_neq0 y =
  H.Pred (Formula.Neq, [y; H.Int 0])

  (*
let get_constraint_by_cross_check y z =
  P.pp "CROSS y: %s\n" (P.pp_list P.pp_formula (List.map snd y));
  P.pp "CROSS z: %s\n" (P.pp_list P.pp_formula (List.map snd z));
  let w = List.combine y z in
  List.map (fun ((vs1, fm1), (vs2, fm2)) ->
      let vs1' = List.map H.mk_var vs1 in
      let fm2' = C.subs_vars vs2 vs1' fm2 in (*  List.fold_left (fun f (a,b) -> U.subs b a f) fm2 vs in *)
      mk_eq fm1 fm2'
    ) w
    (*
  List.fold_left (fun cs (vs1, fm1) ->
      let z' = List.map (fun (vs2, fm1) ->
               List.fold_left (fun f v -> ) fm1 vs2
             ) z in
  
      P.dbg "vs1" (String.concat "." vs1);
      let (_, fm2) = List.find (fun (vs2, _) ->
                         P.dbg "vs2" (String.concat "." vs2);
                         vs2=vs1) z' in
      cs @ [mk_eq fm1 fm2]
    ) [] y *)
;;


let mk_constraints = function
    [] -> []
  | [_] -> []
  | x::xs ->
     let rec aux y = function
         [] -> []
       | z::zs ->
          (get_constraint_by_cross_check y z) @ aux z zs
     in
     aux x xs
;; *)

let mk_constraints_pair (_, zs) =
  match zs with
    [] -> []
  | [_] -> []
  | x::xs ->
     let rec aux (y:H.raw_hflz) = function
         [] -> []
       | z::zs ->
          (mk_eq y z):: aux z zs
     in
     aux x xs
;;

let mk_constraints (xs : (H.raw_hflz * H.raw_hflz) list list) =
  (* let szis = List.concat xs in
  let grp  = List.map fst szis |> List.sort_uniq (fun a b ->
                                      let a' = List.sort String.compare a in
                                      let b' = List.sort String.compare b in
                                      String.compare (String.concat "" a) (String.concat "" b)) in
  let grps = List.map (fun g -> (g, List.filter (fun (x,_) -> List.sort String.compare x= List.sort String.compare g) szis |> List.map snd)) grp in
  let grps' = List.map mk_constraints_pair grps in
  List.concat grps' *)
  let xs' = List.map (fun x -> List.map (fun (a,b) -> mk_eq a b) x) xs in
  List.concat xs' 
;;

let mk_summary_non_zero = function
    [] -> H.Bool true
  | x::xs ->
     let mk_cons_from_edge = function
         [] -> H.Bool true
       | (_,y,_)::ys ->
          let y' = mk_neq0 y in
          List.fold_left (fun b (_, z, _) -> H.mk_or b @@ mk_neq0 z) y' ys
     in
     let x' = mk_cons_from_edge x in
     List.fold_left (fun a x -> H.mk_or a @@ mk_cons_from_edge x) x' xs 

let print_model model =
  List.iter (fun (id, v) -> print_endline (id ^ ": " ^ (string_of_int v))) model;
  print_endline "---";
;;

let subs_by_model model (regex, m, bookmark) =
  let map_model = RH.R.list_to_D model in
  let rf : RH.R.c_re = RH.R.recon map_model bookmark m regex in
  Printf.printf "Reconstructed: %s\n" (RH.R.show_c_re rf);
  rf
;;

let subs_by_model2 model cregex =
  let map_model = RH.R.list_to_D model in
  print_endline "map_model\n";
  let rf : RH.R.c_re = RH.R.crecon map_model cregex in
  Printf.printf "Reconstructed: %s\n" (RH.R.show_c_re rf);
  rf
;;

let rec assign_tag n f =
    match f with
    | H.Bool _ -> f, n
    | H.Var _ -> f, n
    | H.Or (f1, f2) ->
       let f1', n' = assign_tag n f1 in
       let f2', n'' = assign_tag n' f2 in 
       H.mk_or f1' f2', n''
    | H.And (f1, f2) ->
       let f1', n' = assign_tag n f1 in
       let f2', n'' = assign_tag n' f2 in
       H.mk_and f1' f2', n''
    | H.Abs (s, f1) ->
       let f1', n' = assign_tag n f1 in
       H.mk_abs s f1', n'
    | H.App _ ->
       let (p,args) = U.explode_pred f in
       let f' = U.implode_pred p (H.Var "tag"::H.Int n::args) in
       f', n+1
    | H.Int _ -> f, n
    | H.Op _ ->
       f, n
    | H.Pred _ ->
       f, n
    | H.Exists (s, f1) ->
       let f1',n' = assign_tag n f1 in
       H.Exists (s, f1'), n'
    | H.Forall (s, f1) ->
       let f1',n' = assign_tag n f1 in
       H.Forall (s, f1'), n'
;;

let rec remove_tag f =
    match f with
    | H.Bool _ -> f
    | H.Var _ -> f
    | H.Or (f1, f2) ->
       let f1' = remove_tag f1 in
       let f2' = remove_tag f2 in 
       H.mk_or f1' f2'
    | H.And (f1, f2) ->
       let f1' = remove_tag f1 in
       let f2' = remove_tag f2 in
       H.mk_and f1' f2'
    | H.Abs (s, f1) ->
       let f1' = remove_tag f1 in
       H.mk_abs s f1'
    | H.App _ ->
       let (p,args) = U.explode_pred f in
       if List.length args > 0 && List.hd args = H.Var "tag" then
         let f' = U.implode_pred p (List.tl @@ List.tl args) in
         f'
       else
         f
    | H.Int _ -> f
    | H.Op _ ->
       f
    | H.Pred _ ->
       f
    | H.Exists (s, f1) ->
       let f1' = remove_tag f1 in
       H.Exists (s, f1')
    | H.Forall (s, f1) ->
       let f1' = remove_tag f1 in
       H.Forall (s, f1')
;;


let mk_bag splitter transformer goal gnfas defs_map =
  let predicates_in_goals = splitter goal.H.body |> List.map C.exist_free |> List.filter C.is_pred in
  P.pp_list P.pp_formula ~sep:"," predicates_in_goals |> P.dbg "Goal Predicates";
  let n = List.length predicates_in_goals in
  let regex_f = List.map (mk_reg_ex gnfas) predicates_in_goals in
  let connective = L.get_connective goal.H.body in
  (gnfas, regex_f, predicates_in_goals, n, defs_map, goal, connective, transformer)
;;

let rec unfold_formula defs_map n (fltn_unfold_seq:'a list) f =
    match f with
    | H.Bool _ -> f
    | H.Var _ -> f
    | H.Or (f1, f2) ->
       let f1' = unfold_formula defs_map n fltn_unfold_seq f1 in
       let f2' = unfold_formula defs_map n fltn_unfold_seq f2 in 
       H.mk_or f1' f2'
    | H.And (f1, f2) ->
       let f1' = unfold_formula defs_map n fltn_unfold_seq f1 in
       let f2' = unfold_formula defs_map n fltn_unfold_seq f2 in
       H.mk_and f1' f2'
    | H.Abs (s, f1) ->
       let f1' = unfold_formula defs_map n fltn_unfold_seq f1 in
       H.mk_abs s f1'
    | H.App _ ->
       begin
       let (p, args) = U.explode_pred f in
       match args with
         [] ->
          failwith "No arg"
       | H.Var "tag"::n'::args' when L.get_int n'=n ->
          let f' = get_unfolded_formula defs_map (U.implode_pred p args') fltn_unfold_seq in
          f'
       | _ -> f
       end
    | H.Int _ -> f
    | H.Op _ ->
       f
    | H.Pred _ ->
       f
    | H.Exists (s, f1) ->
       H.Exists (s, unfold_formula defs_map n fltn_unfold_seq f1)
    | H.Forall (s, f1) ->
       H.Forall (s, unfold_formula defs_map n fltn_unfold_seq f1)

and get_unfolded_formula defs_map pred_call = function
    [] -> pred_call
  | [_] -> C.exec_unfold defs_map pred_call
  | (_, n)::fltn_unfold_seq ->
     let unfolded = C.exec_unfold defs_map pred_call in
     P.pp "Step Unfolded %s\n" (P.pp_formula unfolded);
     let unfolded',_ = assign_tag 0 unfolded in
     let unfolded' = unfold_formula defs_map n fltn_unfold_seq unfolded' in
     AP.normalize @@ remove_tag unfolded'
;;

let is_possible_to_match goal ys =
  let xs = L.break goal.H.body in
  
  let to_prednames xs = 
    List.filter C.is_pred xs |> List.map U.explode_pred |> List.map fst |> List.sort String.compare in
  let xs' = to_prednames xs in
  let ys' = to_prednames ys in
  xs' = ys'

let mk_pairs goal_body ys =
  let xs = L.get_predicates_ex goal_body |> List.map C.exist_free |> List.map U.explode_pred |> List.map fst in
  
  let eq_classes = List.map (fun xn -> List.filter (fun y ->
                                          let yn = U.explode_pred y |> fst in
                                          yn = xn
                                         ) ys) xs in
  let rec cross = function
      [] -> [[]]
    | z::zs ->
       List.map (fun w -> List.map (fun z' -> z'::w) z) (cross zs) |> List.concat
  in
  cross eq_classes
;;

(*
let try_fold_raw goal n connective perms =
  
  let checked = ref [] in
  let rec match_formulas () =
    
      let perm = Stream.next perms in
      let perm_n, rest = L.take n perm in
      if List.mem perm_n !checked then
        begin
          P.dbg "..:" (string_of_int @@ List.length !checked);
          match_formulas ()
        end
      else
        begin checked := !checked @ [perm_n];
              if is_possible_to_match goal perm_n then
                begin
                  let perm_n' = L.join connective perm_n in
                  P.dbg "To be matched" @@ P.pp_formula goal.H.body;
                  P.dbg "... with" @@ P.pp_formula perm_n';
                  (* let is, f = U.find_matching goal.H.fix goal.H.var goal.H.args goal.H.body perm_n' in *)
                  let is, f = T.fold goal perm_n' in
                  
                  if not is then
                    begin P.pp_formula perm_n' |> P.dbg "Matching failed";
                          match_formulas () end
                  else
                    begin (* let formula = L.join connective perm in *)
                      P.pp_formula perm_n' |> P.dbg "@@@ Matching found @@@";
                      Some (f, rest)
                    end
                end
              else
                match_formulas ()
        end
  in
  let res = try match_formulas () with Stream.Failure -> None in
  res
;; 
 *)

let try_fold_raw transformer goal connective fs =
  P.pp ":::Raw Match::: %s\n" (P.pp_list P.pp_formula fs);
  let prs = mk_pairs goal.H.body (List.filter C.is_pred (List.map C.exist_free fs)) in
  P.pp "prs: %d\n" (List.length prs);
  
  let try_fold goal pr =
    P.pp "prs: %d| %s\n" (List.length pr) (P.pp_list P.pp_formula pr);
    let pr' = List.map transformer pr in
    let perm_n' = L.join connective pr' in
    P.pp "To be matched %s ... with %s\n" (P.pp_formula goal.H.body) (P.pp_formula perm_n');
                  (* let is, f = U.find_matching goal.H.fix goal.H.var goal.H.args goal.H.body perm_n' in *)
    let is, f = C.fold goal perm_n' in
                  
    if not is then
      begin
        None
      end
    else
      begin (* let formula = L.join connective perm in *)
        P.pp_formula perm_n' |> P.dbg "@@@ Matching found @@@";
        let rest = List.filter (fun x -> not (List.mem x pr')) fs in
        Some (f, rest)
      end
    
  in
  
  let try_match r pr =
    if r = None then
      try_fold goal pr
    else
      r
  in
  List.fold_left try_match None prs

   
;; 
       


(*  
let try_unfold_fold goal defs_map gnfas src_perm dest_perm =
  let regexs = List.map2 (mk_reg_ex gnfas) src_perm dest_perm in
  Printf.printf "Regular Expressions: (%s)\n" @@ P.pp_list RH.R.show_gedge regexs;
  let summary_info = List.map mk_constrained_regex regexs in
  let cregexs, aux_constraints, all_bookmarks = List.fold_left (fun (a,b,c) (x,y,z) -> a@[x], b@[y], c@[z]) ([],[],[]) summary_info in
  Printf.printf "Constrained Regular Expressions: (%s)\n" @@ P.pp_list RH.R.show_c_re cregexs;
  Printf.printf "Auxiliary Constraints: (%s)\n" @@ P.pp_list P.pp_formula aux_constraints;

  let abs_summary = List.map RH.R.abs_summary_info cregexs in
  Printf.printf "Computed Size Change: (%s)\n" @@ P.pp_list (P.pp_list (fun (x,a,y) -> Format.sprintf "(%s,%s,%s)" x (P.pp_formula a) y) ~sep:"|") abs_summary;
  let subs_summary = List.map2 (mk_subs_summary defs_map) src_perm abs_summary in
  Printf.printf "Summary Information: (%s)\n"  @@ P.pp_list (P.pp_list (fun (vs, f) -> Format.sprintf "([%s],%s)" (P.pp_list P.id vs) (P.pp_formula f)) ~sep:"|") subs_summary;
  let new_constraints = mk_constraints subs_summary in
  Printf.printf "Constraints: (%s)\n" @@ P.pp_list P.pp_formula new_constraints;
  let neq_constraints = mk_summary_non_zero abs_summary in
  let constraint_vars = List.map (fun xs -> List.map (fun (_,y,_) -> y) xs |> List.map T.fv |> List.concat) abs_summary
                        |> List.concat
                        |> List.sort_uniq String.compare
  in
  let geq_cons = List.map (fun v -> H.Pred (Formula.Ge, [H.Var v;H.Int 0])) constraint_vars in
  let all_constraints = neq_constraints :: aux_constraints @ new_constraints @ geq_cons in

  
  let gen_cons = H.Pred (Formula.Gt, [H.Op (Arith.Add, List.map H.mk_var constraint_vars); H.Int 0]) in
  let model = Z.solve_model_s constraint_vars gen_cons all_constraints in
  print_model model;
  let exact_unfolding_sequences : RegEx.c_re list = List.map (subs_by_model model) all_bookmarks in
  let flatten_unfolding_sequences = List.map RH.R.flatten exact_unfolding_sequences in
  Printf.printf "Flatten: (%s)\n" @@ P.pp_list (P.pp_list (fun (x,i) -> Printf.sprintf "%s:%d" x i) ~sep:"~>") flatten_unfolding_sequences;
  let unfolded_formulas = List.map2 (get_unfolded_formula defs_map) src_perm flatten_unfolding_sequences in
  Printf.printf "Unfoldeds: (%s)\n" @@ P.pp_list P.pp_formula unfolded_formulas;
  let unfolded_goal_body = List.fold_left (fun g (s, d) -> U.subs_f s d g
                             ) goal.H.body (List.combine src_perm unfolded_formulas) in
  Printf.printf "Unfolded goal: (%s)\n" @@ P.pp_formula unfolded_goal_body;
  let res, body = transform goal unfolded_goal_body in
  Printf.printf "Folded goal: (%s)\n" @@ P.pp_formula body;
  res, body
;; *)

let is_formula_folded goal_pred formula =
  L.rec_break formula
  |> List.filter C.is_pred
  |> List.map U.explode_pred
  |> List.map fst
  |> List.exists ((=)goal_pred) 
;;

(*
let try_unfold_fold_stream goal defs_map cycles predicates_in_goals permutation_stream =
  let n = List.length @@ predicates_in_goals in
  let connective = L.get_connective goal.H.body in
  P.pp_list P.pp_formula ~sep:"," predicates_in_goals |> P.dbg "Goal";
  let rec match_formulas () =
    let perm = Stream.next permutation_stream in
    P.pp_list P.pp_formula ~sep:"," perm |> P.dbg "Trying";
    let new_rules, formula =
      try_unfold_fold
        goal
        defs_map
        cycles
        predicates_in_goals
        perm in
    if List.length new_rules > 0 || is_formula_folded goal.H.var formula then
      Some (new_rules, formula)
    else
      begin
        match_formulas ()
      end
  in
  let res = try match_formulas () with Stream.Failure -> None in
  res
;;
 *)

let get_gnfa graph defs_map =
  let rev_graph = RH.get_dest_to_src_graph graph in
  let sc_gnfa  = RH.R.build_gnfa rev_graph in
  let preds = D.fold (fun x _ acc -> acc@[x]) defs_map [] in
  let cycles = List.fold_left (fun acc x ->
                     let gnfa' = RH.reduce sc_gnfa x in
                     D.add x gnfa' acc
                 ) D.empty preds in
  RH.print_gnfa sc_gnfa;
  cycles
;;

let min_req_met predicates_in_goals n preds =
  let sign prs =
    let a = List.map U.explode_pred prs in
    let a' = List.map (fun (x,_) -> (x (*, List.map U.fv ys *))) a in
    a'
  in
  
  List.length preds >= n
  && let pg = sign predicates_in_goals in
     let ps = sign preds in
     List.for_all (fun g -> List.exists ((=)g) ps) pg
;;

let process_r r f predname =
    match r with
    Some (r, params, rest, joiner) ->
     print_endline "Folded!!!";
     let vparams = List.map H.mk_var params in
     let f = U.implode_pred predname vparams in
     (r, joiner (f::rest))
    | None ->
       print_endline "Not Folded!!!";
       [], f
;;


let pred_aligns src goal =
  let (p1, d1) = U.explode_pred src in
  let (p2, d2) = U.explode_pred goal in
  let r = p1=p2 && List.for_all (fun (d1,d2) -> C.fv d1= C.fv d2) (List.combine d1 d2) in
  r
  
  
let rec min_steps defs_map prevs src goal =
  P.pp "src: %s  goal: %s" (P.pp_formula src) (P.pp_formula goal);
  print_endline "";

  if pred_aligns src goal then
    Some []
  else
    if List.length prevs > 0 &&  List.exists (fun a -> pred_aligns a src) prevs then
      begin
        P.pp "all: %s\n" (P.pp_list P.pp_formula prevs);
        None
      end
    else
      begin
      let pred_name, args = U.explode_pred src in
      let rule = D.find pred_name defs_map in
      let nexts = rule.H.body |> L.get_predicates in
      List.fold_left (fun (r,i) predcall ->
          if r=None then
            begin let predname', args' = U.explode_pred predcall in
                  
                  let args'' = C.substitute_args rule.H.args args args' in
                  let pred' = U.implode_pred predname' args'' in
                  P.pp "EEDGE %s  %s\n" (P.pp_formula predcall) (P.pp_formula pred');
                  let r = min_steps defs_map (src::prevs) pred' goal in
                  match r with
                    Some xs -> (Some ((pred_name, predname',args',i)::xs), i+1)
                  | None -> (None, i+1)
            end
          else
            r, i
        ) (None,0) nexts |> fst
      end
;;

let mk_init_path defs_map src_perm pr_goals =
  let rs = List.map2 (fun p -> min_steps defs_map [] p) src_perm pr_goals in
  let paths = List.map (function
                    Some rs ->
                     List.fold_left (fun cr (sn,called_pred,args,tag) ->
                         let called_params = (D.find called_pred defs_map).H.args in
                         
                         let edge = (sn, RH.get_edge @@ List.combine args called_params, called_pred, tag) in
                         let cr1 = RH.R.CChar edge in
                         RH.R.cconcat cr cr1
                       ) (RH.R.CEmpStr) rs
                  | None -> RH.R.CEmpStr
                ) rs in
  paths 
  
let rec unfold_fold bag preds =
  P.pp "Unfold/Fold %s\n" (P.pp_list P.pp_formula preds);
  let (_, _, predicates_in_goals, n, _, _, connective, _) = bag in
  if min_req_met predicates_in_goals n preds then
    begin
    let permutation_stream = L.get_permutation_stream preds in
    let res =
      try
        try_unfold_fold_stream bag permutation_stream
      with
        _ -> None
    in
    match res with
      Some (new_rules, folded_formula, rest) ->
      new_rules, folded_formula, rest
    | None ->
       [], L.join connective preds, []
    end
  else
    begin
      
      [], L.join connective preds, []
    end

and try_unfold_fold_stream bag permutation_stream =
  let (_, _, _, n, _, goal, _, _) = bag in
  let rec match_formulas () =
    let src_perm, rest = Stream.next permutation_stream |> L.take n in
    P.pp_list P.pp_formula ~sep:"," src_perm |> P.dbg "Trying from ";
    let new_rules, folded_formula = try_unfold_fold bag src_perm in
    if List.length new_rules > 0 || is_formula_folded goal.H.var folded_formula then
      Some (new_rules, folded_formula, rest)
    else
      begin
        match_formulas ()
      end
  in
  let res = try match_formulas () with Stream.Failure -> None in
  res

and try_unfold_fold bag src_perm =
  let (_, regex_f, pr_goals, _, defs_map, _, connective, _) = bag in
  let regexs = List.map2 (fun f x -> f x) regex_f src_perm in
  Printf.printf "Regular Expressions: (%s)\n" @@ P.pp_list RH.R.show_gedge regexs;
  let init_path = mk_init_path defs_map src_perm pr_goals in
  Printf.printf "Init path: (%s)\n" @@ P.pp_list RH.R.show_c_re init_path;
  (*
  let simple_solution regexs =
      let summary_info = List.map mk_constrained_regex regexs in
      let cregexs, aux_constraints, all_bookmarks = List.fold_left (fun (a,b,c) (x,y,z) -> a@[x], b@[y], c@[z]) ([],[],[]) summary_info in
      Printf.printf "Constrained Regular Expressions: (%s)\n" @@ P.pp_list RH.R.show_c_re cregexs;
      Printf.printf "Auxiliary Constraints: (%s)\n" @@ P.pp_list P.pp_formula aux_constraints;
      
      let abs_summary = List.map RH.R.abs_summary_info cregexs in
      Printf.printf "Computed Size Change: (%s)\n" @@ P.pp_list (P.pp_list (fun (x,a,y) -> Format.sprintf "(%s,%s,%s)" x (P.pp_formula a) y) ~sep:"|") abs_summary;
      let subs_summary = List.map2 (mk_subs_summary defs_map) src_perm abs_summary in
      Printf.printf "Summary Information: (%s)\n"  @@ P.pp_list (P.pp_list (fun (vs, f) -> Format.sprintf "([%s],%s)" (P.pp_list P.id vs) (P.pp_formula f)) ~sep:"|") subs_summary;
      let new_constraints = mk_constraints subs_summary in
      Printf.printf "Constraints: (%s)\n" @@ P.pp_list P.pp_formula new_constraints;
      (* let neq_constraints = mk_summary_non_zero abs_summary in *)
      let constraint_vars = List.map (fun xs -> List.map (fun (_,y,_) -> y) xs |> List.map C.fv |> List.concat) abs_summary
                            |> List.concat
                            |> List.sort_uniq String.compare
      in
      let geq_cons = List.map (fun v -> H.Pred (Formula.Ge, [H.Var v;H.Int 0])) constraint_vars in
      let all_constraints = (* neq_constraints :: *) aux_constraints @ new_constraints @ geq_cons in
      
      let gen_cons = H.Pred (Formula.Gt, [H.Op (Arith.Add, List.map H.mk_var constraint_vars); H.Int 0]) in
      let model = Z.solve_model_s constraint_vars gen_cons all_constraints in
      print_model model;
      let exact_unfolding_sequences : RegEx.c_re list = List.map (subs_by_model model) all_bookmarks in
      exact_unfolding_sequences
  in *)

  let semi_complex_solution regexs =
    let res = List.map RH.R.get_summary_info regexs in
    let dist_res = List.map (fun (x,y) -> List.map (fun a -> (a,y)) x) res in
    let cross (xs : ('a * 'b) list list) =
      List.fold_left (fun (r:('a * 'b) list list) (zs:('a * 'b) list) ->
          let n = List.map (fun (z:'a * 'b) -> List.map (fun (y:('a * 'b) list) -> y@[z]) r) zs |> List.concat
          in n
        ) [[]] xs
    in
    let cross_res = cross dist_res |> List.filter (fun choice -> List.for_all (fun (a,_) -> a <> RH.R.CEmpStr) choice) in
    let cregexs', aux_constraints = List.hd cross_res |> List.split in
    Printf.printf "Constrained Regular Expressions (org): (%s)\n" @@ P.pp_list RH.R.show_c_re cregexs';
    Printf.printf "Auxiliary Constraints: (%s)\n" @@ P.pp_list P.pp_formula aux_constraints;
    let cregexs = List.map2 RH.R.cconcat init_path cregexs'  in
    Printf.printf "Constrained Regular Expressions (ext): (%s)\n" @@ P.pp_list RH.R.show_c_re cregexs;

    let abs_summary = List.map RH.R.abs_summary_info cregexs in
    Printf.printf "Computed Size Change: (%s)\n" @@ P.pp_list (P.pp_list (fun (x,a,y) -> Format.sprintf "(%s,%s,%s)" x (P.pp_formula a) y) ~sep:"|") abs_summary;
    let subs_summary = List.map2 (mk_subs_summary defs_map pr_goals) src_perm abs_summary in
    Printf.printf "Summary Information: (%s)\n"  @@ P.pp_list (P.pp_list (fun (vs, f) -> Format.sprintf "([%s],%s)" (P.pp_formula vs) (P.pp_formula f)) ~sep:"|") subs_summary;
    
    
    let new_constraints = mk_constraints subs_summary in
    Printf.printf "Constraints: (%s)\n" @@ P.pp_list P.pp_formula new_constraints;
    let neq_constraints = mk_summary_non_zero abs_summary in
    let constraint_vars = List.map (fun xs -> List.map (fun (_,y,_) -> y) xs |> List.map C.fv |> List.concat) abs_summary
                          |> List.concat
                          |> List.sort_uniq String.compare
    in
    let geq_cons0 = List.map (fun v -> H.Pred (Formula.Ge, [H.Var v;H.Int 0])) constraint_vars in
    let gen_cons = H.Pred (Formula.Gt, [H.Op (Arith.Add, List.map H.mk_var constraint_vars); H.Int 0]) in    
    let all_constraints = neq_constraints :: aux_constraints @ new_constraints @ geq_cons0 in
    let model = try
        Z.solve_model_s constraint_vars gen_cons all_constraints
      with
        _ ->
        let all_constraints' = aux_constraints @ new_constraints @ geq_cons0 in
        Z.solve_model_s constraint_vars gen_cons all_constraints'
    in
    
    print_model model;
    P.pp "Z3 Done\n";
    let exact_unfolding_sequences : RegEx.c_re list = List.map (subs_by_model2 model) cregexs in
    P.pp "exact_unfolding_sequences\n";
    exact_unfolding_sequences
  in
    
  let exact_unfolding_sequences = (* simple_solution *) semi_complex_solution regexs in
  
  let flatten_unfolding_sequences = List.map RH.R.flatten exact_unfolding_sequences in
  Printf.printf "Flatten: (%s)\n" @@ P.pp_list (P.pp_list (fun (x,i) -> Printf.sprintf "%s:%d" x i) ~sep:"~>") flatten_unfolding_sequences;
  let unfolded_formulas = List.map2 (get_unfolded_formula defs_map) src_perm flatten_unfolding_sequences in
  Printf.printf "Unfoldeds: (%s)\n" @@ P.pp_list P.pp_formula unfolded_formulas;
  let unfolded_goal_body = L.join connective unfolded_formulas in
  Printf.printf "Unfolded goal: (%s)\n" @@ P.pp_formula unfolded_goal_body;
  
  let res, body = (* timeout *)  (transform bag) unfolded_goal_body (* 60 ([], H.Bool true) *) in
  Printf.printf ">> Unfolding try done\n";
  (* let res = [] in
     let body = H.Bool true in *)
  res, body

(*
and run_in_thread f arg default =
  let pipe_r, pipe_w = Unix.pipe () in
  let t = Thread.create (fun () ->
      let r = f arg in
      let oc = Unix.out_channel_of_descr pipe_w in
      Marshal.to_channel oc (false,r) [];
      close_out oc;
      exit 0
    ) () in
  let tmo = Thread.create (fun () ->
      Thread.delay 60.0;
      Unix.kill (Thread.id t) Sys.sigkill;
      let oc = Unix.out_channel_of_descr pipe_w in
      Marshal.to_channel oc (true,default) [];
      close_out oc;
      Thread.exit ()
    ) () in
  Thread.join t;
  let ic = Unix.in_channel_of_descr pipe_r in
  let r, result = (Marshal.from_channel ic : (bool * (H.hes_rule list * 'b))) in
  result
  *)
  
and timeout (f:H.raw_hflz -> (H.hes_rule list * 'b)) (arg : H.raw_hflz) time (default : (H.hes_rule list * 'b)) =
  let kill pid sign = 
  try Unix.kill pid sign with
  | Unix.Unix_error _ -> Printf.printf "Process %d succeeded\n" pid; exit 0
  | _ -> Printf.printf "Process %d succeeded\n" pid; exit 0
  in
  let pipe_r, pipe_w = Unix.pipe () in
  Printf.printf ">> Forking started %f\n" (Unix.time ());
  (match Unix.fork () with
   | 0 ->
     let x : (H.hes_rule list * 'b) = (f arg) in
     let oc = Unix.out_channel_of_descr pipe_w in
     Marshal.to_channel oc (true,x) [];
     close_out oc;
     exit 0
   | pid0 ->
     Printf.printf ">> Process %d started at %f\n" pid0 (Unix.time ());
     (match Unix.fork () with
        0 ->
        Unix.sleep time;
        kill pid0 Sys.sigkill;
        Printf.printf ">> Process %d timeout at %f\n" pid0 (Unix.time ());
        let oc = Unix.out_channel_of_descr pipe_w in
        Marshal.to_channel oc (false, default) [];
        close_out oc;
        exit 0
      | pid1 ->
        Printf.printf ">> Timeout Process %d for org process %d finished at %f\n" pid1 pid0 (Unix.time ());
        let ic = Unix.in_channel_of_descr pipe_r in
        let rf, result = (Marshal.from_channel ic : (bool * (H.hes_rule list * 'b))) in
        Printf.printf ">> Result retrieved for process (%d) %d finished at %f\n" pid1 pid0 (Unix.time ());
        if rf then ( try Unix.kill pid1 Sys.sigkill with _ -> ()); 
        result ))
  
and transform bag unfolded =
  let (_,_,_,_,_,_,_,transformer) = bag in
  let raw = (* nf connective unfolded in *) transformer unfolded in
  Printf.printf "NF: (%s)\n" @@ P.pp_formula raw;
  let formula = raw_to_formula raw in
  let rs, folded = fold bag formula in
  P.pp "*** Folded to %s\n" (P.pp_formula folded);
  rs, folded
  
and fold bag formula : (H.hes_rule list * H.raw_hflz) =
  let (_, _, _, _, _, _, connective,_) = bag in
  match formula with
    FAnd fs ->
     if connective = L._and then
       fold_formula bag fs
     else if connective = L._or then
       let res = List.map (fold bag) fs in
       let rs, (fs : H.raw_hflz list) = List.split res in
       List.concat rs, list_to_conj fs
     else
        [], formula_to_raw (FAnd fs)
  | FOr fs ->
     if connective = L._or then
       fold_formula bag fs
     else if connective = L._and then
       let res = List.map (fold bag) fs in
       let rs, (fs : H.raw_hflz list) = List.split res in
       List.concat rs, list_to_conj fs
     else
       [], formula_to_raw (FAnd fs) 
  | FExists _ as f ->
     failwith "Existential is not handled at this level"
  | FAtom f -> [], f

and fold_formula bag fs = (** Assumption: the underlying connective of fs is the same as goal connective *)
  let raws = List.map formula_to_raw fs in
  let rs, folded = fold_raw bag raws in
  P.pp "... %s is folded to %s \n" (P.pp_list P.pp_formula raws) (P.pp_formula folded);
  rs, folded

and fold_raw bag fs = (** Assumption: the underlying connective of fs is the same as goal connective *)
  let (_, _, _, _, _, goal, connective, transformer) = bag in

  match try_fold_raw transformer goal connective fs with
    None ->
     P.pp "Matching failed\n";
     let preds, non_preds = List.partition C.is_pred fs in
     let rs, formula', _ = unfold_fold_residual bag preds in
     (* failwith "21"; *)
     let form = formula'::non_preds in
     rs, L.join connective form
     
  | Some (formula, rest) ->
     P.dbg "Fold Status: Success!!: " (P.pp_formula formula);
     P.dbg "Rest: " (P.pp_list P.pp_formula rest);
     let rs, formula2 = fold_raw bag rest in
     
     (* let rs, r_formula, _ = unfold_fold_residual bag preds in *)
     rs, L.join connective (formula::formula2::[])
          (* failwith "22" *) 
     
and unfold_fold_residual bag residual =
  P.dbg "Residual:" (P.pp_list P.pp_formula residual);
  let (_, _, predicates_in_goals, n, _, _, connective, _) = bag in
  P.pp "Count: %d\n" !count;
  if !count > 5 then
    [], L.join connective residual, []
  else
    begin
      count := !count + 1;
      P.pp "Going to Unfold/fold\n";
      let all_rules, folded_formula, rest =  unfold_fold bag residual in
      (* if is_formula_folded goal.H.var folded_formula then
         let new_rule = T.make_new_goal folded_formula in
         new_rule::all_rules, *)
      if min_req_met predicates_in_goals n rest then
        let more_all_rules, more_folded_formula, more_rest = unfold_fold_residual bag rest in
        all_rules @ more_all_rules, L.join connective (folded_formula::more_folded_formula::more_rest), []
      else
        [], L.join connective (folded_formula::rest), []
    end
;;

let mult_unfold_fold transformer splitter goal defs_map predicates_in_f =
  print_endline "~***~***~***~***~***~";
  P.pp "TO BE Folded: %s to the goal %s\n" (P.pp_list P.pp_formula predicates_in_f) (P.pp_rule goal);
  let size_change_graph = RH.get_size_change_graph defs_map in
  print_size_change_graph size_change_graph;
  
  let gnfas = get_gnfa size_change_graph defs_map in
  
  let bag = mk_bag splitter transformer goal gnfas defs_map in
  let (_, _, _, _, _, _, connective, _) = bag in
  let _, folded_goal, rest = unfold_fold bag predicates_in_f in
  (folded_goal::rest) 
;;  

(*
let start_analysis _ goal defs _ =
  let defs_map = C.make_def_map defs in (** Transforms a list to a map *)
  let alldefs =
    begin
      let size_change_graph = RH.get_size_change_graph defs_map in
      print_size_change_graph size_change_graph;

      let gnfas = get_gnfa size_change_graph defs_map in
      let bag = mk_bag goal gnfas defs_map in
      let (_, _, predicates_in_goals, _, _, _, connective) = bag in
      let all_rules, folded_goal, rest = unfold_fold bag predicates_in_goals in
      let goal_rule = C.mk_rule (goal.H.var) goal.H.args goal.H.fix (L.join connective (folded_goal::rest)) in
      (* 
         let permutation_stream = L.get_permutation_stream predicates_in_goals in
      print_endline "--- --- --- --- ---";
      let r = try_unfold_fold_stream
                goal
                defs_map
                gnfas
                predicates_in_goals
                permutation_stream in
      match r with
        Some (new_rules, f) ->
        let goal_pred = {H.var=goal.H.var; args=goal.args; fix=goal.fix; body=f} in
        goal_pred :: new_rules @ defs
      | None ->
         defs *)
      goal_rule::all_rules@defs
    end 
  in
  print_endline "~*~*~*~*~*~*~*~*~*~*~*";    
  let head = List.hd alldefs |> L.make_head in
  let result = head::List.tl alldefs in
  let outtxt1 = P.pp_list ~sep:"\n" P.pp_rule result in
  let outtxt = "%HES\n" ^ outtxt1 in 

  outtxt |> P.dbgn "Result";
  outtxt 
;;

*)
