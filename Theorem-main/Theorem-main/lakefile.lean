import Lake
open Lake DSL

package «Theorem» where
  -- add package configuration options here

lean_lib «Theorem» where

  -- add library configuration options here
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «theorem» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
