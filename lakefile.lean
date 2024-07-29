import Lake
open Lake DSL


package «Theorem» where
  -- add package configuration options here

lean_lib «Theorem» where
  -- add library configuration options here
  -- srcDir := "Theorem_Library_MZ"


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Project» {
  -- add any library configuration options here
}

lean_lib «Lean4Repl» {
  -- add library configuration options here
}

lean_lib «AdaLean» where
