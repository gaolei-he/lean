import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_numbertheory_341
  (a b c : ℕ)
  (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
  (h₁ : Nat.digits 10 ((5^100) % 1000) = [c,b,a]) :
  a + b + c = 13 := by lean_repl sorry
