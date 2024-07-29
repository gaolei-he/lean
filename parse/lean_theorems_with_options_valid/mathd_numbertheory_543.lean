import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_543 :
  (∑ k in (Nat.divisors (30^4)), 1) - 2 = 123 := by lean_repl sorry
