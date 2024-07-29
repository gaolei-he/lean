import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_24
  (x : ℝ)
  (h₀ : x / 50 = 40) :
  x = 2000 := by lean_repl sorry
