import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem imo_1974_p5
  (a b c d s : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : s = a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)) :
  1 < s ∧ s < 2 := by lean_repl sorry
