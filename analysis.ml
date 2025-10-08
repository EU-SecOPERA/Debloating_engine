open Cil_types
open Values

let analysis_dkey =
  Options.register_category ~help:"constant propagation analysis" "analysis"
let rm_dkey = Options.register_category ~help:"debloating project build" "erase"

let singleton_join s1 s2 =
  if Singleton_val.equal s1 s2 then s1 else CNotConstant

let map_join m1 m2 =
  CLval.Map.merge
    (fun _ o1 o2 ->
       match o1, o2 with
       | None, _ | _, None -> Some CNotConstant
       | Some s1, Some s2 -> Some (singleton_join s1 s2))
    m1 m2

let havoc_state s = CLval.Map.map (fun _ -> CNotConstant) s

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
  match (Ast_types.unroll t).tnode, op with
  | TInt k, Neg -> int_result k (Z.neg v)
  | TInt k, BNot -> int_result k (Z.lognot v)
  | TInt k, LNot -> int_result k Z.(if (equal zero v) then one else zero)
  | _ -> CNotConstant

let eval_unop op v t =
  match v with
  | CNotConstant -> CNotConstant
  | CPtr _ -> CNotConstant
  | CConst (CInt64 (v,_,_)) -> eval_int_unop op v t
  | CConst (CReal (v,_,_)) ->
    (match (Ast_types.unroll t).tnode, op with
     | TInt k, LNot -> int_result k (if v = 0. then Z.one else Z.zero)
     | TFloat k, Neg -> CConst (CReal (-. v,k,None))
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
  | Some z when Z.equal z Z.zero -> false_result
  | Some _ -> true_result

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

let rec add_coffset o1 o2 =
  match o1 with
  | CNoOffset -> o2
  | CField(f,o1) -> CField(f, add_coffset o1 o2)
  | CIndex(i,o1) -> CIndex(i, add_coffset o1 o2)

let compute_offset_opt t o =
  let rec aux t o res =
    match o with
    | CNoOffset -> Some res
    | CIndex (i,o) when Ast_types.is_array t ->
      (try
         let elm = Ast_types.direct_element_type t in
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


let eval_cast t v =
  match v with
  | CNotConstant -> CNotConstant
  | CPtr _ when Ast_types.is_ptr t -> v
  | CPtr _ -> CNotConstant
  | CConst (CInt64(z, _, _)) ->
    (match (Ast_types.unroll t).tnode with
     | TInt k -> int_result k z
     | TEnum e -> int_result e.ekind z
     | _ -> CNotConstant)
  | CConst (CReal(v,_,_)) ->
    (match (Ast_types.unroll t).tnode with
     | TFloat k when Cil.isFiniteFloat k v -> CConst (CReal(v,k,None))
     | TFloat _ -> CNotConstant
     | TInt k -> int_result k (Z.of_float v)
     | TEnum e -> int_result e.ekind (Z.of_float v)
     | _ -> CNotConstant)
  | _ -> CNotConstant

let rec eval_exp env e =
  match e.enode with
  | Const c -> eval_const c
  | Lval lv -> eval_lval env lv
  | SizeOf t -> eval_sizeof t
  | SizeOfE e -> eval_sizeof (Cil.typeOf e)
  | AlignOf t -> eval_alignof t
  | AlignOfE e -> eval_alignof (Cil.typeOf e)
  | UnOp (uop,e,t) -> eval_unop uop (eval_exp env e) t
  | BinOp (bop,e1,e2,_) -> eval_binop bop (eval_exp env e1) (eval_exp env e2)
  | CastE (t,e) -> eval_cast t (eval_exp env e)
  | AddrOf lv  -> eval_addrof env lv
  | StartOf lv -> eval_addrof env lv
and eval_addrof env (host,offset) =
  let open Option.Operators in
  (let* b,o =
     match host with
     | Cil_types.Var v -> Some (Var v, CNoOffset)
     | Mem e ->
       (match eval_exp env e with
        | CPtr clv -> Some clv
        | _ -> None)
   in
   let+ o = add_offset env o offset in
   CPtr (b,o)) |> Option.value ~default:CNotConstant

and add_offset env o =
  function
  | NoOffset -> Some o
  | Field(f,co) ->
    let o = add_coffset o (CField (f,CNoOffset)) in
    add_offset env o co
  | Index(i, co) ->
    (match eval_exp env i with
     | CConst (CInt64(z, _, _)) ->
       let o = add_coffset o (CIndex (z, CNoOffset)) in
       add_offset env o co
     | _ -> None)

and eval_lval env lv =
  match eval_addrof env lv with
  | CNotConstant -> CNotConstant
  | CPtr lv ->
    (match CLval.Map.find_opt lv env with
     | Some v -> v
     | None -> CNotConstant)
  | _ -> CNotConstant

let rec init_lval b o init s =
  match init with
  | SingleInit e ->
    CLval.Map.add (b,o) (eval_exp s e) s
  | CompoundInit(_,l) ->
    let eval_one s (o',i) =
      match add_offset s o o' with
      | None -> CLval.Map.add (b,o) CNotConstant s
      | Some o' -> init_lval b o' i s
    in
    List.fold_left eval_one s l

(* TODO: reduce if e is of the form x == c
   (or x != c depending on whether we enter the then or the else branch) *)
let reduce_state_true _e _k s = s

let add_glob_var v i s =
  match i.init with
  | Some (CInit i) -> init_lval (Var v) CNoOffset i s
  | Some (StrInit _) | None -> s

let add_formals kf args s =
  let formals = Kernel_function.get_formals kf in
  let rec aux lf la s =
    match lf,la with
    | [], _ -> s
    | _:: _, [] ->
      Options.fatal "Too few arguments in call to %a" Kernel_function.pretty kf
    | x :: lx, a :: la ->
      aux lx la (CLval.Map.add (Var x, CNoOffset) a s)
  in
  aux formals args s

let add_local_bindings b s =
  List.fold_left (fun s vi -> CLval.Map.add (Var vi, CNoOffset) CNotConstant s)
    s b.blocals

let clear_local_bindings b s =
  let is_based_on_var vi =
    function
    | Var vi' -> Cil_datatype.Varinfo.equal vi vi'
    | _ -> false
  in
  List.fold_left
    (fun s vi -> CLval.Map.filter (fun (h,_) _ -> is_based_on_var vi h) s)
    s b.blocals

let update_offset h o v s =
  match o with
  | None ->
    (* write at an unspecified offset in the structure: just
       invalidate the whole block for now.
       TODO: refine computation by checking which offset is imprecise.
    *)
    CLval.Map.add (h,CNoOffset) CNotConstant s
  | Some o -> CLval.Map.add (h,o) v s

let update_offset_shallow b o v s =
  match o with
  | None ->  update_offset b None v s
  | Some o' ->
    let v' = CLval.Map.find_opt (b,o') s in
    let v' = Option.value v' ~default:CNotConstant in
    update_offset b (Some o') v' s

let shallow_update (b,o) v s1 s2 =
  match b with
  | Cil_types.Var vi ->
    update_offset_shallow (Var vi) (add_offset s1 CNoOffset o) v s2
  | Mem e ->
    (match eval_exp s1 e with
     | CPtr (b,o') -> update_offset_shallow b (add_offset s1 o' o) v s2
     | _ -> havoc_state s2)

let strong_update = update_offset

let assign_lval stmt (h,o as lv) v s1 s2 =
  match h with
  | Cil_types.Var vi -> strong_update (Var vi) (add_offset s1 CNoOffset o) v s2
  | Mem e ->
    (match eval_exp s1 e with
     | CPtr (h',o') -> strong_update h' (add_offset s1 o' o) v s2
     | _ ->
       let aliases = Alias.API.Statement.alias_lvals ~stmt lv in
       let update_one alias s = (shallow_update alias v s1) s in
       Cil_datatype.LvalStructEq.Set.fold update_one aliases s2)

(* counter is shared across branches, not merely mutable. *)
type state =
  { state: Singleton_val.t CLval.Map.t;
    call_stack: Kernel_function.t list;
    malloc_cnt: int ref;
    return_value: Singleton_val.t option
  }

let update_state f s = let state = f s.state in { s with state }

let clear_return s =
  match s.call_stack with
  | [] -> Options.fatal "return outside of a call stack"
  | _::call_stack ->
    { s with return_value = None; call_stack }

module Reachable_stmts =
  State_builder.Set_ref(Cil_datatype.Stmt.Set)(
  struct
    let name = "Debloating.Analysis.Reachable_stmts"
    let dependencies = [ Ast.self; Kernel.MainFunction.self; ]
  end)

module rec Single_values: Interpreted_automata.Domain with type t = state =
struct
  let dkey = analysis_dkey
  type t = state
  let join s1 s2 =
    if s1.malloc_cnt != s2.malloc_cnt then
      Options.fatal "Unshared malloc counter";
    let state = map_join s1.state s2.state in
    { s1 with state }

  let widen s1 s2 =
    let res = join s1 s2 in
    if CLval.Map.equal Singleton_val.equal s1.state res.state then
      Interpreted_automata.Fixpoint
    else Interpreted_automata.Widening res

  let mk_call stmt pre lv kf args =
    Options.debug ~dkey "Considering call to %a" Kernel_function.pretty kf;
    if List.exists (Kernel_function.equal kf) pre.call_stack then begin
      Options.warning "Recursive call detected for %a, approximating"
        Kernel_function.pretty kf;
      Some (update_state havoc_state pre)
    end else begin
      let pre = { pre with call_stack = kf :: pre.call_stack } in
      if Kernel_function.has_noreturn_attr kf then None
      else if Kernel_function.has_definition kf then begin
        let with_formals = update_state (add_formals kf args) pre in
        let res = DataFlow.fixpoint kf with_formals in
        DataFlow.Result.at_return res |>
        Option.map
          (fun s ->
             (match lv with
              | None -> clear_return s
              |   Some lv ->
                let v = Option.value s.return_value ~default:CNotConstant in
                update_state (assign_lval stmt lv v pre.state) s |> clear_return))
      end else begin
        Some (update_state havoc_state (clear_return pre))
      end
    end

  let multiple_calls stmt pre lv args f res =
    let kf = Globals.Functions.get f in
    let new_res = mk_call stmt pre lv kf args in
    match res, new_res with
    | None, r | r, None -> r
    | Some s1, Some s2 ->
      Some (update_state (fun s -> map_join s s2.state) s1)

  let transfer_instr i stmt s =
    match i with
    | Skip _ -> Some s
    | Set (lv, e, _) ->
      let v = eval_exp s.state e in
      Some (update_state (assign_lval stmt lv v s.state) s)
    | Call(lv,f,args,_) ->
      let args = List.map (eval_exp s.state) args in
      (match f with
       | Var f ->
         let kf = Globals.Functions.get f in
         mk_call stmt s lv kf args
       | pf ->
         let loc = Cil_datatype.Instr.loc i in
         let source = fst loc in
         (match eval_lval s.state (pf, NoOffset) with
          | CPtr(Var f,CNoOffset) ->
            let kf = Globals.Functions.get f in
            mk_call stmt s lv kf args
          | _->
            let sf = Alias.API.Statement.alias_vars ~stmt (pf,NoOffset) in
            if Cil_datatype.Varinfo.Set.is_empty sf then begin
              Options.warning ~once:true ~source
                "Empty candidate set for indirect call to %a"
                Printer.pp_lhost pf;
              Some (update_state havoc_state s)
            end else begin
              Cil_datatype.Varinfo.Set.fold
                (multiple_calls stmt s lv args) sf None
            end))
    | Local_init (vi, AssignInit init, _) ->
      Some (update_state (init_lval (Var vi) CNoOffset init) s)
    | Local_init (vi, ConsInit(f, args, kind),loc) ->
      let kf = Globals.Functions.get f in
      let lv = Cil_types.Var vi, NoOffset in
      let ret_lv, args =
        match kind with
        | Plain_func -> Some lv, args
        | Constructor -> None, Cil.mkAddrOf ~loc lv :: args
      in
      let args = List.map (eval_exp s.state) args in
      mk_call stmt s ret_lv kf args
    | Asm _ -> Some (update_state havoc_state s)
    | Code_annot _ -> Some s

  let transfer (_v1, t, _v2) s =
    let open Interpreted_automata in
    match t.edge_transition with
    | Skip -> Some s
    | Return (e,_) ->
      Some { s with return_value = Option.map (eval_exp s.state) e }
    | Guard(e,k,_) ->
      let v = eval_exp s.state e in
      let res, ks = match k with
        | Then -> false_result, "Then"
        | Else -> true_result, "Else"
      in
      Options.debug ~dkey "Evaluating %a to %a"
        Printer.pp_exp e Singleton_val.pretty v;
      let v = compare_val Ne v false_result in
      if Singleton_val.equal v res then begin
        Options.debug ~dkey "Dead branch %s" ks;
        None
      end else Some (update_state (reduce_state_true e k) s)
    | Prop _ -> Some s (*TODO: reduce ACSL annotations. *)
    | Instr (i,stmt) -> transfer_instr i stmt s
    | Enter b ->
      Some (update_state (add_local_bindings b) s)
    | Leave b ->
      Some (update_state (clear_local_bindings b) s)
end
and DataFlow:
  Interpreted_automata.DataflowAnalysis with type state = state =
struct
  include Interpreted_automata.ForwardAnalysis(Single_values)
  let fixpoint ?wto kf pre_state =
    let res = fixpoint ?wto kf pre_state in
    (* unreachable statements are ignored by the iteration. *)
    Result.iter_stmt (fun s _ -> Reachable_stmts.add s) res;
    res
end

(* TODO: real init. *)
let init main_kf is_lib =
  let state =
    if is_lib then
      Globals.Vars.fold
        (fun v _ acc -> CLval.Map.add (Var v, CNoOffset) CNotConstant acc)
        CLval.Map.empty
    else Globals.Vars.fold add_glob_var CLval.Map.empty
  in
  let malloc_cnt = ref 0 in
  { state; malloc_cnt; return_value = None; call_stack = [main_kf] }

let cleanup_fundec f =
  let preserve_labels s =
    if s.labels <> [] then begin
      s.skind <- (Instr (Skip (Cil_datatype.Stmt.loc s)));
      Some s
    end else None
  in
  let remove_locals vars =
    f.slocals <-
      List.filter
        (fun v -> not (List.exists (Cil_datatype.Varinfo.equal v) vars))
        f.slocals
  in
  let rec aux s =
      match s.skind with
      | Block b ->
        cleanup_block b;
        if b.bstmts = [] then begin
          remove_locals b.blocals;
          preserve_labels s
        end else Some s
      | Instr (Skip _) when s.labels = [] -> None
      | If(_,b1,b2,_) ->
          cleanup_block b1;
          cleanup_block b2;
          if b1.bstmts = [] && b2.bstmts = [] then preserve_labels s
          else Some s
      | Loop(_,b,_,_,_) -> cleanup_block b; Some s
      | _ -> Some s
  and cleanup_block b =
    b.bstmts <- List.filter_map aux b.bstmts;
    if b.bstmts = [] then begin
      List.iter (fun v -> v.vdefined <- false) b.blocals
    end
  in
  cleanup_block f.sbody; f

let compute () =
  if not (Reachable_stmts.is_computed ()) then begin
    Alias.Analysis.compute ();
    let main, is_lib = Globals.entry_point () in
    let init_state = init main is_lib in
    let add_formals s =
      List.fold_left
        (fun acc v -> CLval.Map.add (Var v,CNoOffset) CNotConstant acc)
        s (Kernel_function.get_formals main)
    in
    let init_state = update_state add_formals init_state in
    let res = DataFlow.fixpoint main init_state in
    Reachable_stmts.mark_as_computed();
    let s = Kernel_function.find_first_stmt main in
    if Option.is_none (DataFlow.Result.before res s) then
      Options.fatal "Main function is unreachable!"
  end

class debloat_visitor prj =
  let dkey = rm_dkey in
  object(self)
    inherit Visitor.frama_c_refresh prj

    method! vstmt_aux s =
      let loc = Cil_datatype.Stmt.loc s in
      let orig_s = Visitor_behavior.Get_orig.stmt self#behavior s in
      match s.skind with
      | Return _ -> Cil.DoChildren
      | Block _ | UnspecifiedSequence _ -> Cil.DoChildren
      | _ when Reachable_stmts.mem orig_s -> Cil.DoChildren
      | _ ->
        Options.debug ~dkey "Statement %a is dead" Printer.pp_stmt s;  
        s.skind <- Instr (Skip loc); Cil.JustCopy

    method! vfunc _ = Cil.DoChildrenPost cleanup_fundec

    method! vglob_aux =
      function
      | GFun (_, loc) ->
        let kf = Option.get self#current_kf in
        let new_kf = Visitor_behavior.Get.kernel_function self#behavior kf in
        let s = Kernel_function.find_first_stmt kf in
        if Reachable_stmts.mem s then begin
          Options.debug ~dkey "Treating %a" Kernel_function.pretty kf;
          Cil.DoChildren
        end else begin
          Options.debug ~dkey
            "Function %a is never called" Kernel_function.pretty kf;
          let v = Kernel_function.get_vi new_kf in
          v.vdefined <- false;
          let spec = Cil.empty_funspec () in 
          let decl = GFunDecl(spec, v, loc) in
          let formals = Kernel_function.get_formals kf in
          let new_formals =
            List.map
              Visitor.(visitFramacVarDecl (self:>frama_c_visitor)) formals
          in
          Queue.add
            (fun () -> Cil.unsafeSetFormalsDecl v new_formals)
            self#get_filling_actions;
          Cil.ChangeTo [decl]
        end
      | _ -> Cil.JustCopy
  end

let create_debloating_project name =
  let vis prj = new debloat_visitor prj in
  File.create_project_from_visitor name vis

let debloat () =
  compute();
  let prj =
    create_debloating_project (Options.Project_name.get())
  in
  let main_kf, _ = Project.on prj Globals.entry_point () in
  let isRoot =
    function
    | GFun (f,_) ->
      let kf = Globals.Functions.get f.svar in
      Kernel_function.equal kf main_kf
    | _ -> false
  in
  Project.on prj
    (fun () -> Rmtmps.removeUnused ~isRoot (Ast.get ())) ()

let function_called kf =
  compute ();
  Reachable_stmts.mem (Kernel_function.find_first_stmt kf)
