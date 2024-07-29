import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_77
  (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0)
  (h₁ : a ≠ b)
  (h₂ : ∀ x, f x = x^2 + a * x + b)
  (h₃ : f a = 0)
  (h₄ : f b = 0) :
  a = 1 ∧ b = -2 := by lean_repl sorry
