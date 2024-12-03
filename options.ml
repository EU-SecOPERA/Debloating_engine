include Plugin.Register(
    struct
      let name = "debloating"
      let shortname = "debloating"
      let help = "removes code that is unreachable from main entry point"
    end
)


module Enabled =
    False(
      struct
        let option_name = "-debloat"
        let help = "removes code unreachable from main entry point"
  end)

module Project_name =
  String(
    struct
      let option_name = "-debloat-project"
      let arg_name = "s"
      let default = "Debloated"

      let help = "set the name of the project containing the debloated \
                  code to <s> (default name is '" ^ default ^ "')"
end)