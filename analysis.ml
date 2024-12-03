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

let eval_sizeof t =
  try
    let size = Cil.bytesSizeOf t in
   int_constant (Machine.sizeof_kind()) (Z.of_int size)
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

let eval_binop _op v1 v2 _t =
  match v1,v2 with
  | CNotConstant, _ | _, CNotConstant -> CNotConstant
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
  | BinOp (bop,e1,e2,t) -> eval_binop bop (eval_exp env e1) (eval_exp env e2) t
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

let debloat () =
  let result = compute () in
  let prj =
    create_debloating_project (Options.Project_name.get()) result
  in
  Project.on prj
    (fun () -> Rmtmps.removeUnused ~isRoot:(fun _ -> false) (Ast.get ())) ()

let function_called kf =
  let result = compute () in
  DataFlow.Result.before result (Kernel_function.find_first_stmt kf)
  |> Option.is_some
