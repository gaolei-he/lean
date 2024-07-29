import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_321
  (n :  ZMod 1399)
  (h₁ : n = 160⁻¹) :
  n = 1058 := by lean_repl sorry
