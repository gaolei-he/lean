import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_254 :
  (239 + 174 + 83) % 10 = 6 := by lean_repl sorry
