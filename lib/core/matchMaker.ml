open Hflmc2_syntax

module P = Printer
module H = Raw_hflz
module A = ArithmeticProcessor
module Z = Z3Interface
       
let counter = ref 0;;
let newvar () =
  let s = "NV" ^ (string_of_int !counter) in
  counter := !counter + 1;
  s;;

let select_from_two aux fn f f1 f2 =
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
;;

let select_from_one aux fn f f1 =
  let f1', b1 = aux f1 in
  if b1 then
    fn f1', true
  else
    f, false
;;

let  select_from_list aux fn f fs =
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
;;

let (@@) xs ys =
  let ys' = List.filter (fun y -> not (List.mem y xs)) ys in
  xs @ ys'
;;

let div_norm f = f;;

let subs_var to_be by f = 
  let rec aux = function
  | H.Bool _ as f -> f, false
  | H.Var x when x = to_be -> by, true
  | H.Var _ as f -> f, false 
  | H.Or (f1, f2) as f ->
     select_from_two aux (fun f1 f2 -> H.mk_or f1 f2) f f1 f2
  | H.And (f1, f2) as f ->
     select_from_two aux (fun f1 f2 -> H.mk_and f1 f2) f f1 f2
  | H.Abs (s, f1) as f ->
     select_from_one aux (fun f' -> H.mk_abs s f') f f1
  | H.App (f1, f2) as f ->
     select_from_two aux (fun f1 f2 -> H.mk_app f1 f2) f f1 f2
  | H.Int _ as f -> f, false
  | H.Op (o, f1) as f ->
     select_from_list aux (fun f' -> H.mk_op o f') f f1
  | H.Pred (p, f1) as f ->
     H.Pred (p, List.map (fun x -> aux x |> fst) f1) |> A.div_norm, true
  | H.Forall (s, f1) as f ->
     select_from_one aux (fun f' -> H.mk_forall s f') f f1
  | H.Exists (s, f1) as f ->
     select_from_one aux (fun f' -> H.mk_exists s f') f f1
  in
  aux f |> fst
;;


let subs_f to_be by f =

  let rec aux f =
    if f = to_be then by, true else
    match f with
    | H.Bool _ as f -> f, false
    | H.Var _ as f -> f, false 
    | H.Or (f1, f2) as f ->
       select_from_two aux (fun f1 f2 -> H.mk_or f1 f2) f f1 f2
    | H.And (f1, f2) as f ->
       select_from_two aux (fun f1 f2 -> H.mk_and f1 f2) f f1 f2
    | H.Abs (s, f1) as f ->
       select_from_one aux (fun f' -> H.mk_abs s f') f f1
    | H.App (f1, f2) as f ->
       select_from_two aux (fun f1 f2 -> H.mk_app f1 f2) f f1 f2
    | H.Int _ as f -> f, false
    | H.Op (o, f1) as f ->
       select_from_list aux (fun f' -> H.mk_op o f') f f1
    | H.Pred (p, f1) as f ->
       select_from_list aux (fun f' -> H.mk_preds p f') f f1
    | H.Forall (s, f1) as f ->
       select_from_one aux (fun f' -> H.mk_forall s f') f f1
    | H.Exists (s, f1) as f ->
       select_from_one aux (fun f' -> H.mk_exists s f') f f1
  in
  aux f |> fst
;;

let rec subtract s = function
    [] -> []
  | s'::xs when s'=s -> subtract s xs
  | x ::xs -> x::subtract s xs;;

let fv f =
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
  in
  List.sort_uniq String.compare (fv f)
;;

let rec list_to_binary = function
    H.Op (Arith.Add, []) -> H.Int 0
  | H.Op (Arith.Sub, []) -> H.Int 0
  | H.Op (_, []) -> H.Int 1
  | H.Op (_, [x]) -> x
  | H.Op (o, xs) -> 
     List.fold_left (fun acc x -> H.Op (o, [acc;x])) (List.hd xs) (List.tl xs) 
  | H.Pred (Formula.Eq, []) -> H.Bool true
  | H.Pred (_, []) -> H.Bool false
  | H.Pred (_, [x]) -> x
  | H.Pred (o, xs) ->
     begin
       match xs with
         a::b::xs' ->
          let u = H.Pred (o, [a;b]) in
          List.fold_left (fun acc x -> H.And (acc, H.Pred(o, [a;x]))) u xs'
       | _ -> raise A.UnexpectedExpression
     end
  | _ -> raise A.UnexpectedExpression;;

let rec same_set xs ys =
  match xs, ys with
    [], _ -> ys = []
  | _, [] -> false
  | _, y::ys ->
     same_set (List.filter (fun x' -> y <> x') xs) ys
;;

let print_model = function
    None -> print_endline "No model"
  | Some xs ->
     P.pp_list (fun (x,r) -> P.pp_formula x ^ ":=" ^ P.pp_formula r) xs |> P.dbg "Model" 
;;

let add_to_model x r = function
    None -> None
  | Some zs as u ->
     begin
       try
         let (_, r') = List.find (fun (v,_) -> v=x) zs in
         
         if (* A.eval (A.sum_of_mult r) = A.eval (A.sum_of_mult r') *)
           H.Pred (Formula.Eq, [r;r']) |> Z.is_tautology
         then
           u
         else
           None
       with
         Not_found ->
         Some ((x,r)::zs)
     end
;;

let in_model v = function
    None -> false
  | Some xs ->
     List.exists (fun (x,_) -> x=v) xs
;;

let get_model v = function
    None -> raise A.UnexpectedExpression
  | Some xs ->
     try
       List.find (fun (x,_) -> x=v) xs |> snd
     with
       _ -> raise A.UnexpectedExpression
;;

let var_text = function
    H.Var v -> v
  | _ -> raise A.UnexpectedExpression
;;

let rec unify_op u e1 e2 =
  let res =
    match e1, e2 with
      H.Var v, _ ->
       let e2' = A.normalize_v v e2 in
       
       add_to_model e1 e2' u
    | H.Op (_, _), H.Op (_, _) ->
       let e1' = list_to_binary e1 in
       let e2' = list_to_binary e2 in
       unify_arith u e1' e2'
    | _ -> None
  in
  res

and straight_match u e1 e2 =
  match e1, e2 with
    H.Int i1, H.Int i2 -> if i1=i2 then u else None
  | H.Var _, H.Var _ -> add_to_model e1 e2 u
  | H.Op (o1, a1::b1::_), H.Op (o2, a2::b2::_) when o1=o2 ->
     let u1 = straight_match u a1 a2 in
     straight_match u1 b1 b2
  | _, _ -> None

and unify_arith u e1 e2 =
  (* print_endline "unify_arith BEGINs ";
  print_model u;
  P.dbg "e1" (P.pp_formula e1);
  P.dbg "e2" (P.pp_formula e2); *)
  let fv1 = fv e1 in
  let unmodeled_vars, e1' =
    List.fold_left (fun (vs, e) h ->
        let vh = H.Var h in
        if in_model vh u then
          let r = get_model vh u in
          let e' = subs_var h r e in
          (vs,e')
        else
          (h::vs,e)
      ) ([],e1) fv1 in
  (* P.dbg "e1'" (P.pp_formula e1'); *)
  if List.length unmodeled_vars = 0 then
    begin
      if Z.is_tautology (H.Pred (Formula.Eq, [e1';e2])) then
        u
      else
        None
    end
  else
    begin
      let var = List.hd unmodeled_vars in
      let vh = H.mk_var var in
      
      let e1'' = A.normalize e1' in
      let e2'' = A.normalize e2 in

      let a1 = A.sum_of_mult e1'' in
      let a2 = A.sum_of_mult e2'' in
      let (c1,d1) = A.cx_d var e1'' in (* c1*var + d1 *)
      let (c2,d2) = A.cx_d var e2 in (* c2*var + d2 *)
      
      let d = d2 @ (A.neg_list d1) in  (* d2 - d1 *)
      let d' = A.list_div d c1 in (* (d2-d1)/c1 *)
      
      let c' = A.list_div c2 c1 in (* c2/c1 *)
      let r = H.Op(Arith.Add, [H.Op (Arith.Mult, [vh;c']);d']) |> A.normalize_v var in (* var*(c2/c1) + (d2-d1)/c1 *)
      let u' = add_to_model vh r u in
      u'
    end

and set_op u e1 e2 =
  match u with
    None -> None
  | Some u' -> Some ((e1,e2)::u')
 
and unify_list (u : (H.raw_hflz * H.raw_hflz) list option) = function
    [] -> Some []
  | (e1, e2)::args' ->
     let res = 
     match set_op u e1 e2 with
       None -> None
     | Some r1 as u' ->
        match unify_list u' args' with
          None -> None
        | Some r2 -> Some (r1@@r2)
     in
     res
;;

let rec unify_app u args f1 f2 =
  match f1, f2 with
    H.App (g1, h1), H.App (g2, h2) ->
    unify_app u ((h1,h2)::args) g1 g2
  | H.Var s1, H.Var s2 when s1=s2 ->
     unify_list u args
  | _, _ -> None
;;
         
let rec unify_pred u f1 f2 =
  match f1, f2 with
    H.Pred (op1, es1), H.Pred (op2, es2) when op1 = op2 ->
     if List.length es1 = List.length es2 then
       let es12 = List.combine es1 es2 in
       unify_list u es12
     else
       None
  | H.App _, H.App _ ->
     unify_app u [] f1 f2
  | H.Exists (s1, g1), H.Exists (s2, g2) ->
     let g1' = g1 in
     let g2' = subs_var s2 (H.Var s1) g2 in
     unify' u g1' g2'
  | _, _ -> None

and unify_disj u f1 f2 =
  match f1, f2 with
    H.Or (g1, g2), H.Or (h1, h2) ->
     begin
       match unify_disj u g1 h1 with
         None -> None
       | Some r1 as u' ->
          begin
            match unify_disj u' g2 h2 with
              None -> None 
            | Some r2 ->
               Some (r1 @@ r2)
          end
     end
  | _, _ ->
     let r = unify_pred u f1 f2 in
     r

and unify_conj u f1 f2 =
  match f1, f2 with
    H.And (g1, g2), H.And (h1, h2) ->
     begin
       match unify_disj u g1 h1 with
         None -> None
       | Some r1 as u' ->
          begin
            
            match unify_conj u' g2 h2 with
              None -> None 
            | Some r2 ->
               Some (r1 @@ r2)
          end
     end
  | _, _ ->
     let r = unify_disj u f1 f2 in
     r


and unify' u f1 f2 : (H.raw_hflz * H.raw_hflz) list option =
  unify_conj u f1 f2
;;

let subset xs ys =
  List.for_all (fun x -> List.mem x ys) xs
;;

let unify f1 f2 : (H.raw_hflz * H.raw_hflz) list option =
  let u = unify' (Some []) f1 f2 in
  match u with
    None -> None
  | Some sets ->          
     let sets' = List.sort_uniq (fun (x1,y1) (x2,y2) ->
                     if y1=y2 && x1<>x2 then
                       H.compare_raw_hflz x1 x2
                     else
                       let fvs1 = fv y1 in
                       let fvs2 = fv y2 in
                       if subset fvs2 fvs1 then
                         1
                       else
                         if List.length fvs2 < List.length fvs1 then
                           1
                         else
                           -1
                   ) sets
     in
     
     let u' = List.fold_left (fun sets (x,y) -> unify_op sets x y) (Some []) sets' in
     u'
;;

let implode_pred newpredname args =
  let rec implode_pred newpredname = function
      [] -> H.Var newpredname
    | x::xs ->
       let z = implode_pred newpredname xs in
       H.App (z, x)
  in
  implode_pred newpredname (List.rev args)
;;

let get_arg p p_a =
  let pv = H.mk_var p in
  List.find (fun (p',_) ->  pv=p') p_a
  |> snd
;;

let rec find_matching fix _X (params : string list) f f' =
  (* P.pp_formula f' |> P.dbgn "Find Matching";
  P.pp_formula f |> P.dbg "to ";
   *)
  
  let fn = find_matching fix _X params f in
  
  let rec aux = function
      H.Or (f1, f2) ->
       let b1, f1' = fn f1 in
       let b2, f2' = fn f2 in
       b1 || b2, H.mk_or f1' f2'
       
    | H.And (f1, f2) ->
       let b1, f1' = fn f1 in
       let b2, f2' = fn f2 in
       b1 || b2, H.mk_and f1' f2'

    | f ->
       false, f
  in
  
  let m = unify f f' in
  
  match m with
    Some p_a ->
     let args = List.map (fun p -> get_arg p p_a) params in
     true, implode_pred _X args
  | None ->
     aux f'
;;
    
