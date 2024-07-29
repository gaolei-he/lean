import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_388
  (x y z : ℝ)
  (h₀ : 3 * x + 4 * y - 12 * z = 10)
  (h₁ : -2 * x - 3 * y + 9 * z = -4) :
  x = 14 := by lean_repl sorry
