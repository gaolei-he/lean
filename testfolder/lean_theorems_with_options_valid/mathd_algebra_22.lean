import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_22 :
  Real.logb (5^2) (5^4) = 2 := by lean_repl sorry
