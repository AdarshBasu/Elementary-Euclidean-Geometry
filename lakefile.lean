import Lake
open Lake DSL

package «euclid» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    

lean_lib «Euclid» {
  -- add library configuration options here
}

@[default_target]
lean_exe «euclid» {
  root := `Main
}
