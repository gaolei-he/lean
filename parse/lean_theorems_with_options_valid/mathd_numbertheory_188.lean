import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_188 :
  Nat.gcd 180 168 = 12 := by lean_repl sorry
