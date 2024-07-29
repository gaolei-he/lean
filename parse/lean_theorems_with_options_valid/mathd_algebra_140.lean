import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_140
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : ∀ x, 24 * x^2 - 19 * x - 35 = (((a * x) - 5) * ((2 * (b * x)) + c))) :
  a * b - 3 * c = -9 := by lean_repl sorry
