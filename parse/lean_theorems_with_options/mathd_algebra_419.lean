import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_419
  (a b : ℝ)
  (h₀ : a = -1)
  (h₁ : b = 5) :
  -a - b^2 + 3 * (a * b) = -39 := by lean_repl sorry