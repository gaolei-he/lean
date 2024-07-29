import Mathlib.Data.Nat.Choose.Sum

theorem two_mul_succ_sub(hn: n ≤ 2 * n): 2 * n + 1 - n = n + 1 := by
  have two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1  := by
    rw[add_comm]
    rw[Nat.add_sub_assoc hn]
    rw[add_comm]
  rw[two_mul_add_sub]
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  simp
