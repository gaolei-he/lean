import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_412
  (x y : ℝ)
  (h₀ : x + y = 25)
  (h₁ : x - y = 11) :
  x = 18 := by lean_repl sorry
