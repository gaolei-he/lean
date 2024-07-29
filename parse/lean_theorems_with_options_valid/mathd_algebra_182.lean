import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_182
  (y : ℂ) :
  7 * (3 * y + 2) = 21 * y + 14 := by lean_repl sorry
