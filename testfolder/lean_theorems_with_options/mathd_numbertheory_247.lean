import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_247
  (n : ℕ)
  (h₀ : (3 * n) % 2 = 11) :
  n % 11 = 8 := by lean_repl sorry
