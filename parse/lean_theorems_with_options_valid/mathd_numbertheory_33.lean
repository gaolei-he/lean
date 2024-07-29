import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_33
  (n : ℕ)
  (h₀ : n < 398)
  (h₁ : (n * 7) % 398 = 1) :
  n = 57 := by lean_repl sorry
