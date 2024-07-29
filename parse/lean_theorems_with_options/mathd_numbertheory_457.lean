import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_457
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : 80325∣(n!)) :
  17 ≤ n := by lean_repl sorry
