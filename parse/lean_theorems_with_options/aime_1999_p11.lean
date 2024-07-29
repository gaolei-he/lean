import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem aime_1999_p11
  (m : ℚ)
  (h₀ : 0 < m)
  (h₁ : ∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * Real.pi / 180) = Real.tan (m * Real.pi / 180))
  (h₂ : (m.num:ℝ) / m.den < 90) :
  ↑m.den + m.num = 177 := by lean_repl sorry
