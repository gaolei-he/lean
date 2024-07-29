import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12b_2003_p17
  (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : Real.log (x * y^3) = 1)
  (h₂ : Real.log (x^2 * y) = 1) :
  Real.log (x * y) = 3 / 5 := by lean_repl sorry
