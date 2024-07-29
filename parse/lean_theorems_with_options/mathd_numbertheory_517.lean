import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_517 :
  (121 * 122 * 123) % 4 = 2 := by lean_repl sorry
