import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_5
  (n : ℕ)
  (h₀ : 10 ≤ n)
  (h₁ : ∃ x, x^2 = n)
  (h₂ : ∃ t, t^3 = n) :
  64 ≤ n := by lean_repl sorry
