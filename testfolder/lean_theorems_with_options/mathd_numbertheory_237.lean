import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_237 :
  (∑ k in (Finset.range 101), k) % 6 = 4 := by lean_repl sorry
