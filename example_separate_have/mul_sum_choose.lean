import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat

open Finset

open BigOperators

theorem mul_sum_choose : (2 * n + 1) * ∑ k in range n, ((choose (2*n) k):ℝ) = (2 * n + 1) * ((∑ k in range (n+1), ((choose (2*n) k):ℝ)) - ((choose (2*n) n):ℝ) ) := by
  congr 1
  rw[sum_range_succ]
  simp
