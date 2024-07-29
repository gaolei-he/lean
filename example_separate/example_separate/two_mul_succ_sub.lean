import Mathlib.Data.Nat.Choose.Sum
import AdaLean.two_mul_add_sub

theorem two_mul_succ_sub(hn: n ≤ 2 * n): 2 * n + 1 - n = n + 1 := by
  rw[two_mul_add_sub]
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  simp
  exact hn
