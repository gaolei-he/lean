import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_359
  (y : ℝ)
  (h₀ : y + 6 + y = 2 * 12) :
  y = 9 := by lean_repl sorry
