import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_462 :
  ((1 : ℚ)/ 2 + 1 / 3) * (1 / 2 - 1 / 3) = 5 / 36 := by lean_repl sorry
