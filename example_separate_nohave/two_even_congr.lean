import Theorem.example_separate.add_div_two
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators


theorem two_even_congr(hnm: n = 2 * m)(hm : 0 < m) : ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / choose (2 * m) k := by
  rw[hnm]  -- 用 2 * m 替换 n
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  norm_num
