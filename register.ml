let main () = if Options.Enabled.get() then Analysis.debloat ()

let () = Boot.Main.extend main
