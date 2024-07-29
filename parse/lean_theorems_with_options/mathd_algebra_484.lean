import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_484 :
  Real.log 27 / Real.log 3 = 3 := by lean_repl sorry
