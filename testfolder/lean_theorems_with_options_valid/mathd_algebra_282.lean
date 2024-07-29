import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mathd_algebra_282
  (f : ℝ → ℝ)
  (h₀ : ∀ x, (¬ Irrational x) → f x = abs (Int.floor x))
  (h₁ : ∀ x, (Irrational x) → f x = (Int.ceil x)^2) :
  f (8^(1/3)) + f (-Real.pi) + f (Real.sqrt 50) + f (9/2) = 79 := by lean_repl sorry
