import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem amc12a_2002_p6
  (n : ℕ)
  (h₀ : 0 < n) :
  ∃ m, (m > n ∧ ∃ p, m * p ≤ m + p) := by lean_repl sorry
