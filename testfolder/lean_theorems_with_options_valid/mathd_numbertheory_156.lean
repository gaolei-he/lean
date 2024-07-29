import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_156
  (n : ℕ)
  (h₀ : 0 < n) :
  Nat.gcd (n + 7) (2 * n + 1) ≤ 13 := by lean_repl sorry
