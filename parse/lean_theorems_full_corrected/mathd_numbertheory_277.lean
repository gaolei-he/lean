import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_numbertheory_277
  (m n : ℕ)
  (h₀ : Nat.gcd m n = 6)
  (h₁ : Nat.lcm m n = 126) :
  60 ≤ m + n := by lean_repl sorry
