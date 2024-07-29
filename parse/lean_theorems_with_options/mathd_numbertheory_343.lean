import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_343 :
  (∏ k in Finset.range 6, (2 * k + 1)) % 10 = 5 := by lean_repl sorry
