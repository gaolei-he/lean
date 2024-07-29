import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_127 :
  (∑ k in (Finset.range 101), 2^k) % 7 = 3 := by lean_repl sorry
