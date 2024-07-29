import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem algebra_apb4leq8ta4pb4
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b) :
  (a + b)^4 ≤ 8 * (a^4 + b^4) := by lean_repl sorry
