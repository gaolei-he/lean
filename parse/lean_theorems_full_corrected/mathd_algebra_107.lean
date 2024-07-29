import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_107
  (x y : ℝ)
  (h₀ : x^2 + 8 * x + y^2 - 6 * y = 0) :
  (x + 4)^2 + (y-3)^2 = 5^2 := by lean_repl sorry
