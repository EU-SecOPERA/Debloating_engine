let dkey =
  Options.register_category
    ~help:"provides percentage of removed code" "summary"
let () = Options.add_debug_keys dkey

let compute_nb_stmt () =
  let nb_stmt = ref 0 in
  let vis = object
    inherit Visitor.frama_c_inplace
    method! vstmt_aux _ = incr nb_stmt; Cil.DoChildren
    method! vinst _ = Cil.SkipChildren
    method! vexpr _ = Cil.SkipChildren
  end
  in
  Visitor.visitFramacFileSameGlobals vis (Ast.get());
  !nb_stmt

let main () =
  if Options.Enabled.get() then begin
    Analysis.debloat ();
    let nb_stmt_orig = compute_nb_stmt () in
    let nb_stmt_debloat =
      Project.on (Project.from_unique_name (Options.Project_name.get()))
        compute_nb_stmt ()
    in
    let percent_gain = (100 * (nb_stmt_orig - nb_stmt_debloat)) / nb_stmt_orig in
    Options.feedback ~dkey
      "@[<v>Initial number of statements: %d@;\
            Statements after debloating : %d@;\
            percent of statement removed: %d@]"
      nb_stmt_orig nb_stmt_debloat percent_gain
  end

let () = Boot.Main.extend main
