import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_202 :
  (19^19 + 99^99) % 10 = 8 := by lean_repl sorry
