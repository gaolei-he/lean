import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

theorem amc12b_2020_p6
  (n : ℕ)
  (h₀ : 9 ≤ n) :
  ∃ (x : ℕ), (x : ℝ)^2 = ((n + 2)! - (n + 1)!) / n! := by lean_repl sorry
