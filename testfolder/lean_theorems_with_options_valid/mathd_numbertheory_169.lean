import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_169 :
  Nat.gcd 20! 200000 = 40000 := by lean_repl sorry
