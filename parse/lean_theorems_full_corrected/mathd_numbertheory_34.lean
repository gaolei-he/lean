import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_numbertheory_34
  (x: ℕ)
  (h₀ : x < 100)
  (h₁ : x*9 % 100 = 1) :
  x = 89 := by lean_repl sorry
