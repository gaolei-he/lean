import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_362
  (a b : ℝ)
  (h₀ : a^2 * b^3 = 32 / 27)
  (h₁ : a / b^3 = 27 / 4) :
  a + b = 8 / 3 := by lean_repl sorry
