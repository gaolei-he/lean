import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem amc12b_2002_p11
  (a b : ℕ)
  (h₀ : Nat.Prime a)
  (h₁ : Nat.Prime b)
  (h₂ : Nat.Prime (a + b))
  (h₃ : Nat.Prime (a - b)) :
  Nat.Prime (a + b + (a - b + (a + b))) := by lean_repl sorry
