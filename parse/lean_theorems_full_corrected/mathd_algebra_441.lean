import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_441
  (x : ℝ)
  (h₀ : x ≠ 0) :
  12 / (x * x) * (x^4 / (14 * x)) * (35 / (3 * x)) = 10 := by lean_repl sorry
