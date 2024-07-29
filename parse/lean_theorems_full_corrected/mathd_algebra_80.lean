import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_80
  (x : ℝ)
  (h₀ : x ≠ -1)
  (h₁ : (x - 9) / (x + 1) = 2) :
  x = -11 := by lean_repl sorry
