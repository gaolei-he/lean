import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_263
  (y : ℝ)
  (h₀ : 0 ≤ 19 + 3 * y)
  (h₁ : Real.sqrt (19 + 3 * y) = 7) :
  y = 10 := by lean_repl sorry
