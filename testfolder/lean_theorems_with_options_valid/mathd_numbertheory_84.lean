import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_numbertheory_84 :
  Int.floor ((9:ℝ) / 160 * 100) = 5 := by lean_repl sorry
