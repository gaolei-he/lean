import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_208 :
  Real.sqrt 1000000 - 1000000^(1/3) = 900 := by lean_repl sorry
