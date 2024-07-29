import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_37 :
  Nat.lcm 9999 100001 = 90900909 := by lean_repl sorry
