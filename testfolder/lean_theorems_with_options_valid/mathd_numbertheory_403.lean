import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_403 :
  ∑ k in (Nat.properDivisors 198), k = 270 := by lean_repl sorry
