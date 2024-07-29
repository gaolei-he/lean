import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_224
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ Real.sqrt n < 7 / 2 ∧ 2 < Real.sqrt n) :
  S.card = 8 := by lean_repl sorry
