let run () = ()

let main () =
  if Options.Enabled.get() then run ()

let () = Boot.Main.extend main
