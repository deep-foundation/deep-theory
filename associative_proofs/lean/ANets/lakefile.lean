import Lake
open Lake DSL

package «ANets» {
  -- add package configuration options here
}

lean_lib «ANets» {
  -- add library configuration options here
}

@[default_target]
lean_exe «ANets» {
  root := `Main
}
