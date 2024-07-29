import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_354
  (a d : ℝ)
  (h₀ : a + 6 * d = 30)
  (h₁ : a + 10 * d = 60) :
  a + 20 * d = 135 := by lean_repl sorry
