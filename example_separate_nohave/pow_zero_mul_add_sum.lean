import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem pow_zero_mul_add_sum( hn: 0 < n):
((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico 1 n, (-1 : ℝ)^k * (choose (n-1) k : ℝ) * (m / (m+k))) =
∑ k in range n, (-1 : ℝ)^k * (choose (n-1) k : ℝ) * (m / (m+k)) := by
  have h_pow_zero_mul_add: ((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k) : ℝ) * (m / (m+k))) = ((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico (0+1) n, (-1 : ℝ)^k * ((choose (n-1) k) : ℝ) * (m / (m+k))):= by
    congr 1
  rw[h_pow_zero_mul_add, range_eq_Ico, sum_eq_sum_Ico_succ_bot hn]
  simp
