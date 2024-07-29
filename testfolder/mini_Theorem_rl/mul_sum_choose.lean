import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mul_sum_choose : (2 * n + 1) * ∑ k in range n, ((choose (2*n) k):ℝ) = (2 * n + 1) * ((∑ k in range (n+1), ((choose (2*n) k):ℝ)) - ((choose (2*n) n):ℝ) ) := by lean_repl sorry
  congr 1
  rw[sum_range_succ]
  simp
