import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_142
  (m b : ℝ)
  (h₀ : m * 7 + b = -1)
  (h₁ : m * (-1) + b = 7) :
  m + b = 5 := by lean_repl sorry
