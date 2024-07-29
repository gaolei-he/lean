import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem amc12_2000_p1
  (i m o : ℕ)
  (h₀ : i ≠ m ∧ m ≠ o ∧ o ≠ i)
  (h₁ : i*m*o = 2001) :
  i+m+o ≤ 671 := by lean_repl sorry
