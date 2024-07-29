import Lean4Repl
import Mathlib

open Real Nat Topology
open scoped BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem aime_1994_p4
  (n : ℕ)
  (h₀ : 0 < n)
  (h₀ : ∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 k) = 1994) :
  n = 312 := by lean_repl sorry
