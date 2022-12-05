open Hflmc2_syntax
   
module H = Raw_hflz
module D = Map.Make(String)
module P = Printer
module S = Set.Make(Int)
module U = MatchMaker
module AP = ArithmeticProcessor
module R = RegEx
module L = Tools
module C = UFCommon
         
exception StrangeSituation of string
                            
let make_head rule =
  let args = rule.H.args in
  let var = rule.H.var in
  let body = List.fold_left (fun body arg -> H.mk_forall arg body) rule.H.body args in
  let newrule = {H.var=var; args=[]; fix=Fixpoint.Greatest; body=body} in
  newrule
;;

let get_edge p_a : (string * int * string) list =
  let is_const = function
      H.Int _ ->
       true
    | _ ->
       false
  in 
  let get_int = function H.Int i -> i | _ -> raise (StrangeSituation "Not an Int") in
  List.fold_left
    (fun acc (a, p) ->
      let fv = C.fv a in
      if List.length fv = 1 then
        let x = H.mk_var @@ List.hd fv in
        let r = H.Op (Arith.Sub, [a;x]) |> AP.normalize in
        if is_const r then
          (P.pp_formula x, get_int r, p)::acc
        else
          acc
      else
        acc
    ) [] p_a
  

let get_size_change_graph defs_map : ((string * (string * int * string) list) list) D.t =
 let f v =
    let name = v.H.var in
    let params = v.H.args in
    let body = v.H.body in
    let predcalls = L.get_predicates body in
    let f =
      fun predcall ->
      let (called_pred, args) = U.explode_pred predcall in
      let called_params = (D.find called_pred defs_map).H.args in
      let p_a = try List.combine args called_params with e -> raise e in
      let edge = get_edge p_a in
      (called_pred, edge)
    in
    List.map f predcalls
  in
  D.map f defs_map

let print_gnfa gnfa =
  D.iter (fun p x -> Printf.printf "%s = %s\n" p
                     @@ R.show_gedge x) gnfa ;;

let rearrange (gnfa : 'a) =
  let gnfa1 = D.fold (fun dest edges acc ->
                  if R.is_rec dest edges then (dest, edges)::acc else acc
                ) gnfa [] in
  let gnfa2 = D.fold (fun dest edges acc ->
                  if List.exists (fun x -> fst x = dest) acc then
                    acc
                  else
                    acc@[(dest, edges)]
                ) gnfa gnfa1 in
  gnfa2
;;

let are_final gnfa head =
  D.for_all (fun pred body -> if pred = head then true else R.is_final head body) gnfa


let reduce gnfa x =
  let ln = D.cardinal gnfa in
  let rec aux gnfa =
    if are_final gnfa x then
      gnfa
    else
      let gnfa'' = rearrange gnfa in
      let gnfa' =
        List.fold_left (fun gnfa (pred, body) ->
            if pred = x then
              gnfa
            else
            begin (* Printf.printf "Reducing %s\n" pred;
                  Printf.printf "Original %s\n" (R.show_gedge body); *)
                  let body' = R.reduce gnfa x pred body in
                  (* Printf.printf "Reduced %s\n" (R.show_gedge body'); *)
                  D.add pred body' (D.remove pred gnfa)
            end
          ) gnfa gnfa'' in
      aux gnfa'
  in
  let gnfa' = aux gnfa in
  let x_body = D.find x gnfa' in
  (* Printf.printf "Reducing %s\n" x;
  Printf.printf "Original %s\n" (R.show_gedge x_body); *)
  let x_body' = R.eval gnfa' x_body x in
  (* Printf.printf "Reduced %s\n" (R.show_gedge x_body'); *)
  let gnfa'' = D.add x x_body' (D.remove x gnfa') in
  gnfa''

let get_dest_to_src_graph (sc_graph : (string * (string * int * string) list) list D.t) : (string * 'a * int) list D.t =
  D.fold (fun src (edges : (string * 'a) list) acc ->
      List.fold_left (fun (acc,i) (dest, size_changes) ->
          P.pp "... %d to_pred: %s \n" i dest; 
      
          let datas = try D.find dest acc with Not_found -> [] in
          let datas' = datas @ [(src, size_changes, i)] in
          D.add dest datas' (D.remove dest acc), i+1
        ) (acc,0) edges |> fst
    ) sc_graph D.empty
  ;;
  
let test_reg_ex defs_map =
  let sc_graph = get_size_change_graph defs_map in
  
  let rev_graph = get_dest_to_src_graph sc_graph in
  let sc_gnfa  = R.build_gnfa rev_graph in
  let preds = D.fold (fun x _ acc -> acc@[x]) defs_map [] in
  let cycles = List.fold_left (fun acc x ->
                   let gnfa' = reduce sc_gnfa x in
                   D.add x gnfa' acc
                 ) D.empty preds in 
  let preds_pair = List.map (fun x -> List.map (fun y -> (x,y)) preds) preds |> List.concat in
  print_gnfa sc_gnfa;
  List.iter print_endline preds;
  
  List.iter (fun (x,y) -> 
      let gnfa' = D.find x cycles in
      let gnfa'' = reduce gnfa' y in
      let y_body = D.find y gnfa'' in
      Printf.printf "%s \\to %s:& %s \\\\ \n" x y (R.show_gedge y_body);
      let m = R.newvar () in
      let y_body' = R.simplify_alter y_body in
      let cy_body, f , s = y_body' |> R.straight m [] in
      let f' = R.mk_and f (R.eq m R.one) in
      Printf.printf "Concrete:& %s\\\\ \n" (R.show_c_re cy_body);
      Printf.printf "& %s, \\\\\n" (P.pp_formula f');

      let rf = R.recon D.empty s m y_body' in
      Printf.printf "Reconstructed:& %s\\\\\\\\\n" (R.show_c_re rf);
      (* let cy_body, cs = R.simplify_alter y_body |> R.f R.one in
      List.iter (fun cy_body -> Printf.printf "Concrete: %s\n" (R.show_c_re cy_body)) cy_body;
      List.iter (fun y -> Printf.printf "%s, \n" (R.show_raw_hflz y)) [cs]; *)
      
    ) preds_pair ;
  ()
;;



let permute lst =
  let rec range i n =
    if i=n then [] else i::range (i+1) n in
  let nth i s =
    let ls = S.elements s in
    let ls' = List.sort (fun a b -> a-b) ls in
    List.nth ls' i in
  let lstar = Array.of_list lst in
  let len   = Array.length lstar in
  let ks    = range 1 (len + 1) in
  let indices = S.of_list (range 0 len) in
  let choose k (v, indices, res) =
    let idx = v mod k in
    let ix = try (nth idx indices) with _ -> print_endline ("Not actually found " ^ (string_of_int idx)); raise Not_found in
    (v / k, S.remove ix indices, lstar.(ix) :: res)
  in
  let perm i =
    let (v, _, res) =
      List.fold_right choose ks (i, indices, [])
    in
    if v > 0 then None else Some res
  in
  Stream.from perm
;;

(*
let start_analysis _ goal defs _ =
  (* let inp = ['a';'b';'c';'d';'e'] in
  let xxxs = permute inp in
  let xxxx = Stream.npeek (fact (List.length inp)) xxxs in 
  List.iter (fun xs -> List.iter (fun y -> print_char y) xs; print_char '\n') xxxx; *)
  let defs_map = C.make_def_map defs in
  let alldefs =
    begin
      P.dbg "Regex-mode" "";
      let queue = Queue.create () in
      (* let unfoldeds = unfold_all_pred goal.H.body defs_map in
      List.iter (fun uf -> Queue.push uf queue) unfoldeds; *)
      Queue.push goal.H.body queue;
      (* let max = 2 in *)
      let res = test_reg_ex defs_map in
      (* match res with
        Some (r, x, _) ->
         P.pp_formula x |> P.dbg "@@Matched";
         P.pp_rule r |> P.dbg "@@New rule";
         let goal_pred = {H.var=goal.H.var; args=goal.args; fix=goal.fix; body=x} in
         goal_pred::r::defs
         
      | None -> P.dbg "!!! Matched None" ""; failwith "Not folded" *)
      defs
    end
  in
  print_endline "~*~*~*~*~*~*~*~*~*~*~*";    
  let head = List.hd alldefs |> make_head in
  let result = head::List.tl alldefs in
  let outtxt1 = P.pp_list ~sep:"\n" P.pp_rule result in

  let outtxt = "%HES\n" ^ outtxt1 in 
  outtxt |> P.dbgn "Result";

  outtxt
 *)
