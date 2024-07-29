import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem algebra_bleqa_apbon2msqrtableqambsqon8b
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : b ≤ a) :
  (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by lean_repl sorry
