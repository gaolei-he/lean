import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_45 :
  (Nat.gcd 6432 132) + 11 = 23 := by lean_repl sorry
