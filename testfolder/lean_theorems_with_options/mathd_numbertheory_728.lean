import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_728 :
  (29^13 - 5^13) % 7 = 3 := by lean_repl sorry
