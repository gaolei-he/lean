import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem imo_1990_p3
  (n : ℕ)
  (h₀ : 2 ≤ n)
  (h₁ : n^2 ∣ 2^n + 1) :
  n = 3 := by lean_repl sorry
