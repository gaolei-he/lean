import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_13
  (u v : ℕ)
  (S : Set ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 0 < n ∧ (14 * n) % 100 = 46)
  (h₁ : IsLeast S u)
  (h₂ : IsLeast (S \ {u}) v) :
  ((u + v) : ℚ) / 2 = 64 := by lean_repl sorry
