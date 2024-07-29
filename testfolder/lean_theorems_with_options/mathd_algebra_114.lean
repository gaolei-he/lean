import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_114
  (a : ℝ)
  (h₀ : a = 8) :
  (16 * (a^2)^(1 / 3))^(1 / 3) = 4 := by lean_repl sorry
