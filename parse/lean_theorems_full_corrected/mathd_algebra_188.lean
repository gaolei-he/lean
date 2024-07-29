import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem mathd_algebra_188
  (σ : Equiv ℝ ℝ)
  (h : σ.1 2 = σ.2 2) :
  σ.1 (σ.1 2) = 2 := by lean_repl sorry
