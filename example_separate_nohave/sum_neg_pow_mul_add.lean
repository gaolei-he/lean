import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_neg_pow_mul_add( hn: 0 < n):
∑ k in Ico 1 n, (-1 : ℝ) ^ k * ((Nat.choose (n - 1) (k - 1)) : ℝ) * (m / (m + k)) + (-1 : ℝ)^n * (choose n n : ℝ) * (m / (m+n)) = ∑ k in Ico 1 (n+1), (-1 : ℝ) ^ k * ((Nat.choose (n - 1) (k - 1)) : ℝ) * (m / (m + k)) := by
  have h1:  1 ≤ n := by linarith
  rw[sum_Ico_succ_top h1]
  simp
