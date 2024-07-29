import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem algebra_2rootsintpoly_am10tap11eqasqpam110
  (a : ℂ) :
  (a - 10) * (a + 11) = a^2 + a - 110 := by lean_repl sorry
