import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_99
  (n : ℕ)
  (h₀ : (2 * n) % 47 = 15) :
  n % 47 = 31 := by lean_repl sorry
