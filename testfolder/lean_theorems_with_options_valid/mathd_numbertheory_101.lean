import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_101 :
  (17 * 18) % 4 = 2 := by lean_repl sorry
