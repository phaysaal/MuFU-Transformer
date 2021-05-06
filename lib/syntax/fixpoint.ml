open MuFU_util
type t = Least | Greatest
  [@@deriving eq,ord,show,iter,map,fold,sexp]
