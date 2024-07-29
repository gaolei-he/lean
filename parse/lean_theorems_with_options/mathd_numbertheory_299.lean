import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_299 :
  (1 * 3 * 5 * 7 * 9 * 11 * 13) % 10 = 5 := by lean_repl sorry
