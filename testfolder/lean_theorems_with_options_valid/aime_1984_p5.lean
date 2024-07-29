import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem aime_1984_p5
  (a b : ℝ)
  (h₀ : Real.logb 8 a + Real.logb 4 (b^2) = 5)
  (h₁ : Real.logb 8 b + Real.logb 4 (a^2) = 7) :
  a * b = 512 := by lean_repl sorry
