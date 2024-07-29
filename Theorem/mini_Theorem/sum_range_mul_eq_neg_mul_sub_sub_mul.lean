import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_range_mul_eq_neg_mul_sub_sub_mul {n : ℕ} : ∑ k in range (n+1), k * choose (2*n) (n-k)
      = ∑ k in range (n+1), (-1 : ℝ) * (n-k-n) * choose (2*n) (n-k) := by
      rw [cast_sum (range (n + 1)) fun x => x * Nat.choose (2 * n) (n - x)]
      refine' sum_congr rfl fun k hk => _
      rw [cast_mul]
      congr 1
      norm_num
