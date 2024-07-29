import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12a_2021_p22
  (a b c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^3 + a * x^2 + b * x + c)
  (h₁ : f⁻¹' {0} = {Real.cos (2 * Real.pi / 7), Real.cos (4 * Real.pi / 7), Real.cos (6 * Real.pi / 7)}) :
  a * b * c = 1 / 32 := by lean_repl sorry
