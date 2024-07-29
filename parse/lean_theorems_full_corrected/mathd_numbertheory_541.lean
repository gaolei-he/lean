import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_numbertheory_541
  (m n : ℕ)
  (h₀ : 1 < m)
  (h₁ : 1 < n)
  (h₂ : m * n = 2005) :
  m + n = 406 := by lean_repl sorry
