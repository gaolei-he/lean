import Mathlib.Data.Real.Basic
import AdaLean.choose_mul_eq_mul_sub'
import AdaLean.choose_sub_sub

open Nat

open Finset

open BigOperators

theorem bot_sum_mul_congr : ∑ k in range (n+1), ((k * choose (2 * n + 1) k):ℝ) = (2 * n + 1) * ∑ k in range n, ((choose (2*n) k):ℝ) := by
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot]
  simp
  rw[choose_sub_sub]
  rw[mul_sum]
  rw[sum_Ico_eq_sum_range]
  simp
  linarith
