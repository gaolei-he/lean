import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem aime_1983_p9
  (x : ℝ)
  (h₀ : 0 < x ∧ x < Real.pi) :
  12 ≤ ((9 * (x^2 * (Real.sin x)^2)) + 4) / (x * Real.sin x) := by lean_repl sorry
