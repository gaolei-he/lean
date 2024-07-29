import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem aime_1991_p6
  (r : ℝ)
  (h₀ : ∑ k in Finset.Icc (19 : ℕ) 91, (Int.floor (r + k / 100)) = 546) :
  Int.floor (100 * r) = 743 := by lean_repl sorry
