import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_numbertheory_293
  (n : ℕ)
  (h₀ : n ≤ 9)
  (h₁ : 11∣20 * 100 + 10 * n + 7) :
  n = 5 := by lean_repl sorry