import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem aime_1983_p2
  (x p : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < p ∧ p < 15)
  (h₁ : p ≤ x ∧ x ≤ 15)
  (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
  15 ≤ f x := by lean_repl sorry
