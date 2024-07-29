import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_range_halfway_choose_symm {n : ℕ} (h : 0 < n) : ∑ k in range n, choose (2 * n - 1) k
            = ∑ k in range n, choose (2 * n - 1) (2 * n - 1 - k) := by
  refine' sum_congr rfl fun y hy => _
  have : y ≤ 2 * n - 1 := by
    have h1 : y < n := mem_range.1 hy
    refine le_pred_of_lt ?h
    have h2 : n < 2 * n := by exact lt_two_mul_self h
    exact Nat.lt_trans h1 h2
  rw [choose_symm this]
