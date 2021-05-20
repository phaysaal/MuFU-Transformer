open Hflmc2_syntax
   
module H = Raw_hflz

let counter = ref 0;;
let newvar () =
  let s = ".." ^ (string_of_int !counter) in
  counter := !counter + 1;
  s;;
  
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
;;
         
let rec unify_arith e1 e2 =
  match e1, e2 with
    H.Var _, _ -> Some [(e1, e2)]
  | H.Op (op1, es1), H.Op (op2, es2) when op1=op2 ->
     if List.length es1 = List.length es2 then
       let es12 = List.combine es1 es2 in
       unify_list es12
     else
       None
  | _ -> None

and unify_list = function
    [] -> Some []
  | (e1, e2)::args' ->
     match unify_arith e1 e2 with
       None -> None
     | Some r1 ->
        match unify_list args' with
          None -> None
        | Some r2 -> Some (r1@r2)
;;

let rec unify_app args f1 f2 =
  match f1, f2 with
    H.App (g1, h1), H.App (g2, h2) ->
    unify_app ((h1,h2)::args) g1 g2
  | H.Var s1, H.Var s2 when s1=s2 ->
     unify_list args
  | _, _ -> None
;;
         
let rec unify_pred f1 f2 =
  match f1, f2 with
    H.Pred (op1, es1), H.Pred (op2, es2) when op1 = op2 ->
     if List.length es1 = List.length es2 then
       let es12 = List.combine es1 es2 in
       unify_list es12
     else
       None
  | H.App _, H.App _ ->
     unify_app [] f1 f2
  | H.Exists (s1, g1), H.Exists (s2, g2) ->
     let nv = H.Var (newvar ()) in
     let g1' = subs_var s1 nv g1 in
     let g2' = subs_var s2 nv g2 in
     unify g1' g2'
  | _, _ -> None

and unify_disj f1 f2 =
  match f1, f2 with
    H.Or (g1, g2), H.Or (h1, h2) ->
     begin
       match unify_disj g1 h1 with
         None -> None
       | Some r1 ->
          begin
            match unify_disj g2 h2 with
              None -> None 
            | Some r2 ->
               Some (r1 @ r2)
          end
     end
  | _, _ ->
     unify_pred f1 f2

and unify_conj f1 f2 =
  match f1, f2 with
    H.And (g1, g2), H.Or (h1, h2) ->
     begin
       match unify_disj g1 h1 with
         None -> None
       | Some r1 ->
          begin
            match unify_disj g2 h2 with
              None -> None 
            | Some r2 ->
               Some (r1 @ r2)
          end
     end
  | _, _ ->
     unify_pred f1 f2


and  unify f1 f2 : (H.raw_hflz * H.raw_hflz) list option =
  unify_conj f1 f2
