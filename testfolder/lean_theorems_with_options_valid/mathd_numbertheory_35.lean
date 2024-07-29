import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_35
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∣ (Nat.sqrt 196)) :
  ∑ k in S, k = 24 := by lean_repl sorry
