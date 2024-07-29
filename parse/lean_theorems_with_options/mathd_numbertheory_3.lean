import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_3 :
  (∑ x in Finset.range 10, ((x + 1)^2)) % 10 = 5 := by lean_repl sorry
