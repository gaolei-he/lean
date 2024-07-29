import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_176
  (x : ℝ) :
  (x + 1)^2 * x = x^3 + 2 * x^2 + x := by lean_repl sorry
