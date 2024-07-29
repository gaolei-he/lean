import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_207 :
  8 * 9^2 + 5 * 9 + 2 = 695 := by lean_repl sorry
