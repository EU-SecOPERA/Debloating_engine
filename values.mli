open Cil_types
type base_addr = Var of varinfo | Dynamic of int
type constant_offset =
    CNoOffset
  | CField of fieldinfo * constant_offset
  | CIndex of Z.t * constant_offset

type clval = base_addr * constant_offset

type singleton_val = CConst of constant | CPtr of clval | CNotConstant

module Base_addr: Datatype.S_with_collections with type t = base_addr

module Constant_offset:Datatype.S_with_collections with type t = constant_offset

module CLval : Datatype.S_with_collections with type t = clval

module Singleton_val : Datatype.S with type t = singleton_val
