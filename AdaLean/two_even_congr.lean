import AdaLean.add_div_two
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators


theorem two_even_congr(hnm: n = 2 * m)(hm : 0 < m) : ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / choose (2 * m) k := by
  rw[hnm]
  rw [sum_range_succ]
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot]
  simp
  rw[add_comm, ← add_assoc]
  norm_num
  linarith