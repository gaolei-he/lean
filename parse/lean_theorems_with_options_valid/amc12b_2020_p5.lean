import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12b_2020_p5
  (a b : ℕ)
  (h₀ : (5 : ℚ)/8 * b = 2/3 * a + 7)
  (h₁ : (b : ℚ) - 5/8 * b = (a - 2/3 * a) + 7) :
  a = 42 := by lean_repl sorry
