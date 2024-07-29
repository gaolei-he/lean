import Mathlib.Data.Nat.Choose.Sum
import AdaLean.two_mul_succ_sub
import AdaLean.sum_choose_symm

open Nat

open Finset

open BigOperators


theorem sum_choose_eq_Ico (hn: n ≤ 2 * n): ∑ k in range n, choose (2 * n) k = ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by
  rw [range_eq_Ico]
  rw[sum_choose_symm]
  rw[sum_Ico_reflect]
  simp
  rw[two_mul_succ_sub]
  linarith
  linarith
