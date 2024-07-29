import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators


theorem sum_choose_eq_Ico (hn: n ≤ 2 * n): ∑ k in range n, choose (2 * n) k = ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by
  rw [range_eq_Ico]
  have h1 : ∑ k in Ico 0 n, Nat.choose (2 * n) k = ∑ k in Ico 0 n, Nat.choose (2 * n) (2 * n - k) := by
    refine' sum_congr rfl fun y hy ↦ _
    have yn : y < n := by exact (mem_Ico.1 hy).2
    have y2n : y ≤ 2 * n := by linarith
    rw[← choose_symm y2n]
  rw[h1]
  rw[sum_Ico_reflect]
  simp
  have two_mul_succ_sub : 2 * n + 1 - n = n + 1 := by
    have two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1  := by
      rw[add_comm]
      rw[Nat.add_sub_assoc hn]
      rw[add_comm]
    rw[two_mul_add_sub]
    simp
    have h23: 2 * n - n = 2 * n - 1 * n := by simp
    rw[h23]
    rw[← Nat.mul_sub_right_distrib]
    simp
  rw[two_mul_succ_sub]
  linarith
