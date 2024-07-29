import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778
  (r : ℝ)
  (h₀ : r^(1 / 3) + 1 / r^(1 / 3) = 3) :
  r^3 + 1 / r^3 = 5778 := by lean_repl sorry
