open Cil_types

type base_addr =
  | Var of varinfo
  | Dynamic of int (* we track individual malloc calls *)

type constant_offset =
  | CNoOffset
  | CField of fieldinfo * constant_offset
  | CIndex of Integer.t * constant_offset

module Base_addr = Datatype.Make_with_collections(
  struct
    include Datatype.Serializable_undefined
    type t = base_addr

    let name = "Debloating.Analysis.base_addr"

    let structural_descr = Structural_descr.t_abstract

    let reprs = Dynamic 0 ::
                List.map (fun x -> Var x) Cil_datatype.Varinfo.reprs

    let compare ba1 ba2 =
      match ba1, ba2 with
      | Var v1, Var v2 -> Cil_datatype.Varinfo.compare v1 v2
      | Dynamic v1, Dynamic v2 -> Stdlib.compare v1 v2
      | Var _, _ -> -1
      | Dynamic _, Var _ -> 1

    let equal = Datatype.from_compare

    let hash = function
      | Var v -> 17 * Cil_datatype.Varinfo.hash v
      | Dynamic i -> 43 * Hashtbl.hash i

    let pretty fmt = function
      | Var v -> Cil_datatype.Varinfo.pretty fmt v
      | Dynamic i -> Format.fprintf fmt "Malloc'ed Block %d" i

  end
)

module Constant_offset = Datatype.Make_with_collections(
    struct
      include Datatype.Serializable_undefined
      type t = constant_offset
      let name = "Debloating.Values.Constant_offset"

      let structural_descr = Structural_descr.t_abstract

      let reprs =
        CNoOffset :: CIndex (Z.zero,CNoOffset)::
        (List.map (fun f -> CField (f, CNoOffset)) Cil_datatype.Fieldinfo.reprs)

      let rec compare o1 o2 =
        match o1, o2 with
        | CNoOffset, CNoOffset -> 0
        | CNoOffset, _ -> -1
        | _, CNoOffset -> 1
        | CField (f1, o1), CField (f2, o2) ->
          let res = Cil_datatype.Fieldinfo.compare f1 f2 in
          if res <> 0 then res else compare o1 o2
        | CField _, _ -> -1
        | _, CField _ -> 1
        | CIndex (i1,o1), CIndex(i2,o2) ->
          let res = Z.compare i1 i2 in
          if res <> 0 then res else compare o1 o2

      let equal = Datatype.from_compare

      let hash o =
        match o with
        | CNoOffset -> 17
        | CField (f, _) -> 23 * Cil_datatype.Fieldinfo.hash f
        | CIndex (i, _) -> 59 * Hashtbl.hash i

      let rec pretty fmt o =
        match o with
        | CNoOffset -> Format.fprintf fmt "@;"
        | CField(f,o) ->
          Format.fprintf fmt "@;.%a%a"
            Cil_datatype.Fieldinfo.pretty f
            pretty o
        | CIndex(i,o) ->
          Format.fprintf fmt "@;@[<h>[%a]@]@;%a" Z.pp_print i pretty o

    end)

module CLval =
  Datatype.Pair_with_collections(Base_addr)(Constant_offset)
    (struct let module_name = "Debloating.Value.CLval" end)

type clval = CLval.t

type singleton_val =
  | CConst of constant
  | CPtr of clval
  | CNotConstant

module Singleton_val = Datatype.Make(
  struct
    include Datatype.Serializable_undefined
    type t = singleton_val

    let name = "Debloating.Analysis.singleton_val"
    let structural_descr = Structural_descr.t_abstract

    let reprs =
      List.map (fun x -> CConst x) Cil_datatype.Constant.reprs
      @ List.map (fun x -> CPtr x) CLval.reprs

    let compare c1 c2 =
      match c1, c2 with
      | CConst c1, CConst c2 -> Cil_datatype.Constant.compare c1 c2
      | CConst _, _ -> -1
      | _, CConst _ -> 1
      | CPtr lv1, CPtr lv2 -> CLval.compare lv1 lv2
      | CPtr _, _ -> -1
      | _, CPtr _-> 1
      | CNotConstant, CNotConstant -> 0

    let equal = Datatype.from_compare

    let pretty fmt = function
    | CConst c -> Printer.pp_constant fmt c
    | CPtr lv -> Format.fprintf fmt "&(%a)" CLval.pretty lv
    | CNotConstant -> Format.pp_print_string fmt "Top"
  end
)
