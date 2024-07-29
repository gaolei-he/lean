import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_302 :
  (Complex.I / 2)^2 = -(1 / 4) := by lean_repl sorry
