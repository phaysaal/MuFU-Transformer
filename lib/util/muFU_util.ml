module Core = Core
open Core

module Pair = struct
  (* Bifunctor method *)
  let bimap  ~f (x, y) = (f x, f y)
  let first  ~f (x, y) = (f x, y)
  let second ~f (x, y) = (x, f y)
end

module List = struct
  include List
  let enumurate xs =
    List.zip_exn xs (List.init (List.length xs) ~f:(fun x -> x))
  let find_with_index ~f:(p : 'a -> bool) (xs : 'a list) =
    List.find_exn (enumurate xs) ~f:(fun (x,_) -> p x)
  let rec powerset = function
    | [] -> [[]]
    | x :: xs ->
       let ps = powerset xs in
       ps @ List.map ~f:(fun ss -> x :: ss) ps
  let rec powerset_with_limit n = function
    | [] -> if n >= 0 then [[]] else []
    | x :: xs ->
        let ps = powerset_with_limit n xs in
        let ps'= powerset_with_limit (n-1) xs in
        ps @ List.map ~f:(fun ss -> x :: ss) ps'
  let powerset ?limit xs = match limit with
    | None -> powerset xs
    | Some n -> powerset_with_limit n xs
  let singleton x = [x]
  let cartesian_products : 'a list list -> 'a list list =
    fun xss ->
      fold_right xss ~init:[[]] ~f:begin fun xs acc ->
        map (cartesian_product xs acc) ~f:begin fun (y,ys) -> y::ys end
      end
  let zipper_map ~f =
    function
    | [] -> []
    | x::xs ->
        let rec go xs y zs =
          f xs y zs ::
            match zs with
            | [] -> []
            | z::zs -> go (y::xs) z zs
        in go [] x xs
  let remove_duplicates : 'a list -> equal:('a -> 'a -> bool) -> 'a list =
    fun xs ~equal ->
      let cons_if_uniq x xs = if mem ~equal xs x then xs else x :: xs in
      List.fold_left xs ~init:[] ~f:begin fun xs x ->
        cons_if_uniq x xs
      end
  let subset xs ys =
    for_all xs ~f:begin fun x ->
      exists ys ~f:begin fun y ->
        x = y end end

  let rec maximals
       : 'a list
      -> compare:('a -> 'a -> int option)
      -> 'a list =
    fun xs ~compare ->
      let remove_lt x ys =
        let is_maximal = ref true in
        let rec go x ys =
          match ys with
          | [] -> []
          | y::ys ->
              begin match compare x y with
              | Some n when n >= 0 ->
                  go x ys
              | Some _ ->
                  is_maximal := false;
                  y :: go y ys
              | None ->
                  y :: go x ys
              end
        in
        let ys' = go x ys in
        (!is_maximal, ys')
      in
      match xs with
      | [] -> []
      | x::xs ->
          let (is_maximal, ys) = remove_lt x xs in
          if is_maximal
          then x :: maximals ~compare ys
          else maximals ~compare ys
  let maximals' (<=) xs =
    let compare a b =
      let a_le_b = a <= b in
      let b_le_a = b <= a in
      match () with
      | _ when a_le_b && b_le_a -> Some 0
      | _ when a_le_b           -> Some (-1)
      | _ when b_le_a           -> Some 1
      | _                       -> None
    in
    maximals ~compare xs
end

module Unit = Unit

module Int = Int

module Bool = Bool

module Array = Array

module String   = String

module Map = struct
  include Map
  module Make'(Key : Key) = struct
    include Make(Key)
    let replace : 'a t -> key:Key.t -> data:'a -> 'a t =
      fun map ~key ~data ->
        let map = remove map key in
        add_exn map ~key ~data
    let merge' : 'a t -> 'a t -> 'a t =
      fun m1 m2 ->
        merge m1 m2
          ~f:begin fun ~key -> function
          | `Left x -> Some x
          | `Right x -> Some x
          | `Both _ ->
              invalid_arg @@ "merge: " ^ string_of_sexp (Key.sexp_of_t key)
          end
  end
end
module IntMap   = Map.Make'(Int)
module StrMap   = Map.Make'(String)

module Set      = struct
  include Set
  module Make'(Elt : Elt) = struct
    include Make(Elt)
    let maximals' (<=) set =
      to_list set |> List.maximals' (<=) |> of_list
  end
end
module IntSet   = Set.Make'(Int)
module StrSet   = Set.Make'(String)

module Option   = Option

module Sexp     = Sexp

module Hashtbl  = Hashtbl

module Hash_set = Hash_set

module Arg      = Arg
module Command  = Command

module In_channel = In_channel
module Out_channel = Out_channel

module Void = struct
  type t = Void of { absurd : 'a. 'a }
  let absurd (Void void) = void.absurd
  let equal v _     = absurd v
  let compare v _   = absurd v
  let pp _ v        = absurd v
  let t_of_sexp _   = failwith "void_of_sexp"
  let sexp_of_t v   = absurd v
end

module Fn = struct
  include Fn

  exception Fatal of string
  exception Unsupported of string
  exception TODO of string
  let fatal s = raise (Fatal s)
  let unsupported ?(info="") () = raise (Unsupported info)
  let todo ?(info="") () = raise (TODO info)

  let neg i = -i
  let const x _ = x

  let print ?(tag="") pp x =
    (* if tag = ""
    then Format.printf "@[%a@]@." pp x
    else *) Format.printf "%s: @[%a@]@." tag pp x
  ;;

  
  let on injection g x y = g (injection x) (injection y)

  let curry f x y = f (x, y)
  let uncurry f (x,y) = f x y

  let ( <<< ) f g x = f (g x)
  let ( >>> ) f g x = g (f x)
  let ( -$- ) f x y = f y x

  let read_file file = In_channel.(with_file file ~f:input_all)

  let assert_no_exn f =
    try f () with e -> print_endline (Exn.to_string e); assert false

  let run_command ?(timeout=20.0) cmd =
    let f_out, fd_out = Unix.mkstemp "/tmp/run_command.stdout" in
    let f_err, fd_err = Unix.mkstemp "/tmp/run_command.stderr" in
    let process_status = Lwt_main.run @@
      Lwt_process.exec
        ~timeout
        ~stdout:(`FD_move fd_out)
        ~stderr:(`FD_move fd_err)
        ("", cmd)
    in
    let stdout = read_file f_out in
    let stderr = read_file f_err in
    Unix.remove f_out;
    Unix.remove f_err;
    (process_status, stdout, stderr)

  class counter = object
    val mutable cnt = 0
    method tick =
      let x = cnt in
      cnt <- x + 1;
      x
  end
end


let (>>>) = Fn.(>>>)
let (<<<) = Fn.(<<<)
let (-$-) = Fn.(-$-)

let char_of_sexp      = char_of_sexp
let sexp_of_char      = sexp_of_char
let bool_of_sexp      = bool_of_sexp
let sexp_of_bool      = sexp_of_bool
let sexp_of_exn       = sexp_of_exn
let float_of_sexp     = float_of_sexp
let sexp_of_float     = sexp_of_float
let int_of_sexp       = int_of_sexp
let sexp_of_int       = sexp_of_int
let int32_of_sexp     = int32_of_sexp
let sexp_of_int32     = sexp_of_int32
let int64_of_sexp     = int64_of_sexp
let sexp_of_int64     = sexp_of_int64
let list_of_sexp      = list_of_sexp
let sexp_of_list      = sexp_of_list
let nativeint_of_sexp = nativeint_of_sexp
let sexp_of_nativeint = sexp_of_nativeint
let option_of_sexp    = option_of_sexp
let sexp_of_option    = sexp_of_option
let sexp_of_ref       = sexp_of_ref
let string_of_sexp    = string_of_sexp
let sexp_of_string    = sexp_of_string
let bytes_of_sexp     = bytes_of_sexp
let sexp_of_bytes     = sexp_of_bytes
let unit_of_sexp      = unit_of_sexp
let sexp_of_unit      = sexp_of_unit

module Logs     = Logs
module Logs_cli = Logs_cli
module Logs_fmt = Logs_fmt

type ('a, 'b) result = Ok of 'a | Error of 'b
