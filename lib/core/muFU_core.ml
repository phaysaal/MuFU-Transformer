open MuFU_syntax
open Transformer
   
module H = Raw_hflz 

let transform hes : H.hes =
  let hes' = transform_hes hes in
  hes'
    
