import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_303
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 2 ≤ n ∧ 171 ≡ 80 [MOD n] ∧ 468 ≡ 13 [MOD n]) :
  ∑ k in S, k = 111 := by lean_repl sorry
