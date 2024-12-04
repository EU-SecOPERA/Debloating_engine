open Cil_types
open Values

let singleton_join s1 s2 =
  if Singleton_val.equal s1 s2 then s1 else CNotConstant

let map_join m1 m2 =
  Base_addr.Map.merge
    (fun _ o1 o2 ->
       match o1, o2 with
       | None, _ | _, None -> Some CNotConstant
       | Some s1, Some s2 -> Some (singleton_join s1 s2))
    m1 m2

let eval_const c = CConst c

let int_constant k i = CConst(CInt64(i,k,None))

let eval_sizeof_int t = Z.of_int (Cil.bytesSizeOf t)

let eval_sizeof t =
  try
    int_constant (Machine.sizeof_kind()) (eval_sizeof_int t)
  with Cil.SizeOfError _ -> CNotConstant

let eval_alignof t =
  try
    let align = Cil.bytesAlignOf t in
    int_constant (Machine.sizeof_kind()) (Z.of_int align)
  with Cil.SizeOfError _ -> CNotConstant

let int_result k i =
  let res, truncated = Cil.truncateInteger64 k i in
  if truncated && Cil.isSigned k then CNotConstant
  else int_constant k res

let true_result = int_result IBool Z.one
let false_result = int_result IBool Z.zero

let eval_int_unop op v t =
  match Cil.unrollType t, op with
  | TInt (k,_), Neg -> int_result k (Z.neg v)
  | TInt (k,_), BNot -> int_result k (Z.lognot v)
  | TInt (k,_), LNot -> int_result k Z.(if (equal zero v) then one else zero)
  | _ -> CNotConstant

let eval_unop op v t =
  match v with
  | CNotConstant -> CNotConstant
  | CPtr _ -> CNotConstant
  | CConst (CInt64 (v,_,_)) -> eval_int_unop op v t
  | CConst (CReal (v,_,_)) ->
    (match Cil.unrollType t, op with
     | TInt (k, _), LNot -> int_result k (if v = 0. then Z.one else Z.zero)
     | TFloat(k,_), Neg -> CConst (CReal (-. v,k,None))
     | _ -> CNotConstant)
  | CConst (CEnum ei) ->
    let v =
      match Cil.constFoldToInt ei.eival with
      | None ->
        Options.fatal "Enum item %a has a non-constant value %a"
          Printer.pp_varname ei.einame Printer.pp_exp ei.eival
      | Some v -> v
    in
    eval_int_unop op v t
  | _ -> CNotConstant

let is_cmp = function Lt | Gt | Le | Ge | Eq | Ne -> true | _ -> false

let eval_eq_operands = function
  | Eq | Le | Ge -> true_result
  | Gt | Lt | Ne -> false_result
  | _ -> Options.fatal "operator is not a comparison"

let eval_lt_operands = function
  | Lt | Le | Ne -> true_result
  | Eq | Ge | Gt -> false_result
  | _ -> Options.fatal "operator is not a comparison"

let eval_gt_operands = function
  | Gt | Ge | Eq -> true_result
  | Ne | Le | Lt -> false_result
  | _ -> Options.fatal "operator is not a comparison"

let rec compare_offset op o1 o2 =
  match o1, o2 with
  | CNoOffset, CNoOffset -> eval_eq_operands op
  | CNoOffset, CIndex (i, o2) when Z.equal i Z.zero -> compare_offset op o1 o2
  | CIndex (i, o1), CNoOffset when Z.equal i Z.zero -> compare_offset op o1 o2
  | CNoOffset, CField(fi, o2) when fst (Cil.fieldBitsOffset fi) = 0 ->
    compare_offset op o1 o2
  | CField(fi,o1), CNoOffset when fst (Cil.fieldBitsOffset fi) = 0 ->
    compare_offset op o1 o2
  | CNoOffset, _ -> eval_lt_operands op
  | _, CNoOffset -> eval_gt_operands op
  | CIndex(i1, o1), CIndex(i2, o2) ->
    (match Z.compare i1 i2 with
     | 0 -> compare_offset op o1 o2
     | n when n < 0 -> eval_lt_operands op
     | _ -> eval_gt_operands op)
  | CIndex _, _ | _, CIndex _ -> CNotConstant
  | CField(fi1,o1), CField(fi2,o2) ->
    let open Cil_datatype in
    if (Fieldinfo.equal fi1 fi2 ||
        (Compinfo.equal fi1.fcomp fi2.fcomp && not fi1.fcomp.cstruct))
    then compare_offset op o1 o2
    else if fi1.forder < fi2.forder then eval_lt_operands op
    else eval_gt_operands op

let compare_lval op (b1,o1) (b2,o2) =
  if Base_addr.equal b1 b2 then begin
    compare_offset op o1 o2
  end else begin
    if op = Eq then false_result
    else if op = Ne then true_result
    else CNotConstant
  end

let compare_c_const op c1 c2 =
  let loc = Cil_datatype.Location.unknown in
  let open Cil_builder.Exp in
  let c1 = of_constant c1 in
  let c2 = of_constant c2 in
  let cmp = binop op c1 c2 in
  match Cil.constFoldToInt (cil_exp ~loc cmp) with
  | None -> CNotConstant
  | Some z when Z.equal z Z.zero -> eval_eq_operands op
  | Some z when Z.lt z Z.zero -> eval_lt_operands op
  | Some _ -> eval_gt_operands op

let compare_val op v1 v2 =
  match v1, v2 with
  | CNotConstant, _ | _, CNotConstant -> CNotConstant
  | CPtr lv1, CPtr lv2 -> compare_lval op lv1 lv2
  | CPtr _, _ | _, CPtr _ -> CNotConstant
  | CConst c1, CConst c2 -> compare_c_const op c1 c2

let add_index (b,o) z =
  let rec aux =
    function
    | CNoOffset -> CIndex(z,CNoOffset)
    | CIndex (z1,CNoOffset) -> CIndex(Z.add z1 z, CNoOffset)
    | CIndex (z, o) -> CIndex(z, aux o)
    | CField(f,o) -> CField(f, aux o)
  in
  CPtr (b, aux o)

let compute_offset_opt t o =
  let rec aux t o res =
    match o with
    | CNoOffset -> Some res
    | CIndex (i,o) when Cil.isArrayType t ->
      (try
         let elm = Cil.typeOf_array_elem t in
         let sz = eval_sizeof_int elm in
         aux elm o (Z.(res + sz * i))
       with
       | Cil.SizeOfError _ -> None)
    | CIndex _ -> None
    | CField (f,o) ->
      let open Option.Operators in
      let* fo = f.foffset_in_bits in
      let fo = fo / 8 in
      aux f.ftype o Z.(add res (of_int fo))
  in aux t o Z.zero

let diff_offset (b1,o1) (b2,o2) =
  if Base_addr.equal b1 b2 then begin
    let base_type =
      match b1 with
      | Var v -> v.vtype
      | Dynamic _ -> Cil_builder.Type.(cil_typ (array char))
    in
    let open Option.Operators in
    (let+ o1 = compute_offset_opt base_type o1
     and* o2 = compute_offset_opt base_type o2 in
     int_result (Machine.ptrdiff_kind()) (Z.sub o1 o2)) |>
    Option.value ~default:CNotConstant
  end else CNotConstant

let eval_binop op v1 v2 =
  match v1,v2 with
  | _ when is_cmp op -> compare_val op v1 v2
  | CNotConstant, _ | _, CNotConstant -> CNotConstant
  | CPtr lv1, CConst (CInt64 (z,_,_)) ->
    (match op with
     | PlusPI -> add_index lv1 z
     | MinusPI -> add_index lv1 (Z.neg z)
     | _ -> Options.fatal
              "Unexpected pointer operand for %a" Printer.pp_binop op)
  | CPtr lv1, CPtr lv2 when op = MinusPP -> diff_offset lv1 lv2
  | CPtr _, _ | _, CPtr _ ->
    Options.fatal "Unexpected pointer operand for %a" Printer.pp_binop op
  | CConst c1, CConst c2 ->
    let loc = Cil_datatype.Location.unknown in
    let open Cil_builder.Exp in
    let c1 = of_constant c1 in
    let c2 = of_constant c2 in
    let op = binop op c1 c2 in
    match (Cil.constFold true (cil_exp ~loc op)).enode with
    | Const c -> CConst c
    | _ -> CNotConstant


let eval_cast _t v =
  match v with
  | CNotConstant -> CNotConstant
  | _ -> CNotConstant

let rec eval_exp env e =
  match e.enode with
  | Const c -> eval_const c
  | Lval lv -> eval_lval env lv
  | SizeOf t -> eval_sizeof t
  | SizeOfE e -> eval_sizeof (Cil.typeOf e)
  | SizeOfStr s ->
    int_constant (Machine.sizeof_kind ()) (Z.of_int (String.length s))
  | AlignOf t -> eval_alignof t
  | AlignOfE e -> eval_alignof (Cil.typeOf e)
  | UnOp (uop,e,t) -> eval_unop uop (eval_exp env e) t
  | BinOp (bop,e1,e2,_) -> eval_binop bop (eval_exp env e1) (eval_exp env e2)
  | CastE (t,e) -> eval_cast t (eval_exp env e)
  | AddrOf lv  -> eval_addrof env lv
  | StartOf lv -> eval_addrof env lv
and eval_addrof _env (_host,_offset) = CNotConstant
and eval_lval _env (_host,_offset) = CNotConstant

let add_glob_var v i s =
  let init =
    match i.init with
    | None -> CNotConstant
    | Some (SingleInit e) -> eval_exp Base_addr.Map.empty e
    | Some (CompoundInit (_,_l)) ->
      Options.not_yet_implemented
        ~source:(fst v.vdecl) "Compound Initialization"
  in
  Base_addr.Map.add (Var v) init s

(* counter is shared across branches, not merely mutable. *)
type state =
  { state: Singleton_val.t Base_addr.Map.t; malloc_cnt: int ref }

let update_state f s = let state = f s.state in { s with state }

module rec Single_values: Interpreted_automata.Domain with type t = state =
  struct
    type t = state
    let join s1 s2 =
      if s1.malloc_cnt != s2.malloc_cnt then
        Options.fatal "Unshared malloc counter";
      let state = map_join s1.state s2.state in
      { s1 with state }

    let widen s1 s2 =
      let res = join s1 s2 in
      if Base_addr.Map.equal Singleton_val.equal s1.state res.state then
        Interpreted_automata.Fixpoint
      else Interpreted_automata.Widening res

    let transfer _ _ _s = None
  end
and DataFlow:
  Interpreted_automata.DataflowAnalysis with type state = state =
  Interpreted_automata.ForwardAnalysis(Single_values)

(* TODO: real init. *)
let init is_lib =
  let state =
    if is_lib then
      Globals.Vars.fold
        (fun v _ acc -> Base_addr.Map.add (Var v) CNotConstant acc)
        Base_addr.Map.empty
    else Globals.Vars.fold add_glob_var Base_addr.Map.empty
  in
  let malloc_cnt = ref 0 in
  { state; malloc_cnt }

(* TODO: memoize computation. *)
let compute () =
  let main, is_lib = Globals.entry_point () in
  let init_state = init is_lib in
  let add_formals s =
    List.fold_left
      (fun acc v -> Base_addr.Map.add (Var v) CNotConstant acc)
      s (Kernel_function.get_formals main)
  in
  let init_state = update_state add_formals init_state in
  DataFlow.fixpoint main init_state

class debloat_visitor prj result =
  object(self)
    inherit Visitor.frama_c_refresh prj

    method! vvdec v =
      let vorig = Visitor_behavior.Get_orig.varinfo self#behavior v in
      let v = { v with vtemp = true } (* mark it as removable. *) in
      Visitor_behavior.Set.varinfo self#behavior vorig v;
      Visitor_behavior.Set_orig.varinfo self#behavior v vorig;
      Cil.ChangeDoChildrenPost(v,fun x->x)

    method! vstmt_aux s =
      let loc = Cil_datatype.Stmt.loc s in
      match DataFlow.Result.before result s with
      | None -> s.skind <- Instr (Skip loc); Cil.SkipChildren
      | Some _ -> Cil.DoChildren

    method! vglob_aux =
      function
      | GFun (f, loc) ->
        let decl = GFunDecl(Cil.empty_funspec(), f.svar, loc) in
        Cil.ChangeDoChildrenPost([decl], fun x -> x)

      | _ -> Cil.JustCopy
  end

let create_debloating_project name result =
  let vis prj = new debloat_visitor prj result in
  File.create_project_from_visitor name vis

module Debloating_done =
  State_builder.False_ref(
    struct
      let name = "Analysis.Debloating_done"
      let dependencies = [ Ast.self; Options.Project_name.self ]
    end)

let debloat () =
  if not (Debloating_done.get()) then begin
    Debloating_done.set true;
    let result = compute () in
    let prj =
      create_debloating_project (Options.Project_name.get()) result
    in
    Project.on prj
      (fun () -> Rmtmps.removeUnused ~isRoot:(fun _ -> false) (Ast.get ())) ();
  end

let function_called kf =
  let result = compute () in
  DataFlow.Result.before result (Kernel_function.find_first_stmt kf)
  |> Option.is_some
