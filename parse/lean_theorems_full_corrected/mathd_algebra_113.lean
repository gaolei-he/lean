import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_113
  (x : ℝ) :
  x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3 := by lean_repl sorry
