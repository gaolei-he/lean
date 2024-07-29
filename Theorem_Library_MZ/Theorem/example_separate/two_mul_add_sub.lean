import Mathlib.Data.Nat.Choose.Sum


theorem two_mul_add_sub (hn: n ≤ 2 * n): 2 * n + 1 - n = 2 * n - n + 1  := by
    rw[add_comm]
    rw[Nat.add_sub_assoc hn]
    rw[add_comm]


theorem two_mul_add_sub_from_0_to_0(n : ℕ)(hn : n ≤ 2 * n)(gol:  1 + 2 * n - n = 2 * n - n + 1) :
   2 * n + 1 - n = 2 * n - n + 1 := by
  rw[add_comm]
  apply gol

theorem two_mul_add_sub_from_0_to_1(n : ℕ)(hn : n ≤ 2 * n)(gol:  1 + (2 * n - n) = 2 * n - n + 1) :
   2 * n + 1 - n = 2 * n - n + 1 := by
  rw[add_comm]
  rw[Nat.add_sub_assoc hn]
  apply gol

theorem two_mul_add_sub_from_0_to_2(n : ℕ)(hn : n ≤ 2 * n) :
   2 * n + 1 - n = 2 * n - n + 1 := by
  rw[add_comm]
  rw[Nat.add_sub_assoc hn]
  rw[add_comm]

theorem two_mul_add_sub_from_1_to_1(n : ℕ)(hn : n ≤ 2 * n)(gol:  1 + (2 * n - n) = 2 * n - n + 1) :
   1 + 2 * n - n = 2 * n - n + 1 := by
  rw[Nat.add_sub_assoc hn]
  apply gol

theorem two_mul_add_sub_from_1_to_2(n : ℕ)(hn : n ≤ 2 * n) :
   1 + 2 * n - n = 2 * n - n + 1 := by
  rw[Nat.add_sub_assoc hn]
  rw[add_comm]

theorem two_mul_add_sub_from_2_to_2(n : ℕ)(hn : n ≤ 2 * n) :
   1 + (2 * n - n) = 2 * n - n + 1 := by
  rw[add_comm]

