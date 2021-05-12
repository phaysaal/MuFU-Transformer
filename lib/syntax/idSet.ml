open Hflmc2_util
include Set.Make'(Id.Key)
let singleton : 'a. 'a Id.t -> t =
  fun v -> singleton (Id.remove_ty v)
let remove : 'a. t -> 'a Id.t -> t =
  fun set x -> remove set (Id.remove_ty x)
let mem set x = mem set (Id.remove_ty x)
let add set x = add set (Id.remove_ty x)
