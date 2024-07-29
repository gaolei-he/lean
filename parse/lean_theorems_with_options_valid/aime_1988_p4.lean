import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem aime_1988_p4
  (n : ℕ)
  (a : ℕ → ℝ)
  (h₀ : ∀ n, abs (a n) < 1)
  (h₁ : ∑ k in Finset.range n, (abs (a k)) = 19 + abs (∑ k in Finset.range n, a k)) :
  20 ≤ n := by lean_repl sorry
