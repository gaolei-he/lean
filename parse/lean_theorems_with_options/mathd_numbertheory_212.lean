import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_212 :
  (16^17 * 17^18 * 18^19) % 10 = 8 := by lean_repl sorry
