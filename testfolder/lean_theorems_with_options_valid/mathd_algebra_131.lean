import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_131
  (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 2 * x^2 - 7 * x + 2)
  (h₁ : f a = 0)
  (h₂ : f b = 0)
  (h₃ : a ≠ b) :
  1 / (a - 1) + 1 / (b - 1) = -1 := by lean_repl sorry
