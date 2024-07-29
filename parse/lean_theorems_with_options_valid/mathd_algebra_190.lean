import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_190 :
  ((3 : ℝ) / 8 + 7 / 8) / (4 / 5) = 25 / 16 := by lean_repl sorry
