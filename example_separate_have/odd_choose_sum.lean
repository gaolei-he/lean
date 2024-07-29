import Mathlib.Data.Real.Basic
import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem odd_choose_sum(hnm: n = 2 * m + 1): ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ ) ^ k / choose (2 * m + 1) k := by
  rw[hnm]
  rw[sum_range_succ]
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot hm2]
  norm_num
