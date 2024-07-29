import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_536 :
  ↑3! * ((2 : ℝ)^3 + Real.sqrt 9) / 2 = (33 : ℝ) := by lean_repl sorry
