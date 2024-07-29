import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_400
  (x : ℝ)
  (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) :
  x = 50 := by lean_repl sorry
