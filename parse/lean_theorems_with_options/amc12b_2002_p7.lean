import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12b_2002_p7
  (a b c : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : b = a + 1)
  (h₂ : c = b + 1)
  (h₃ : a * b * c = 8 * (a + b + c)) :
  a^2 + (b^2 + c^2) = 77 := by lean_repl sorry
