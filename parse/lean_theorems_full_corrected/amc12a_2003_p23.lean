import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem amc12a_2003_p23
  (S : Finset ℕ)
  (h₀ : ∀ (k : ℕ), k ∈ S ↔ 0 < k ∧ ((k * k) : ℕ) ∣ (∏ i in (Finset.Icc 1 9), i!)) :
  S.card = 672 := by lean_repl sorry
