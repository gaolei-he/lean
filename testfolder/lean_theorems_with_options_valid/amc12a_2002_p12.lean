import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12a_2002_p12
  (f : ℝ → ℝ)
  (k : ℝ)
  (a b : ℕ)
  (h₀ : ∀ x, f x = x^2 - 63 * x + k)
  (h₁ : f a = 0 ∧ f b = 0)
  (h₂ : a ≠ b)
  (h₃ : Nat.Prime a ∧ Nat.Prime b) :
  k = 122 := by lean_repl sorry
