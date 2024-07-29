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


theorem two_mul_succ_sub_from_0_to_0(n : ℕ)(hn : n ≤ 2 * n)(gol:  2 * n + 1 - n = n + 1) :
   2 * n + 1 - n = n + 1 := by
  have two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1  := by
    rw[add_comm]
    rw[Nat.add_sub_assoc hn]
    rw[add_comm]
  apply gol

theorem two_mul_succ_sub_from_0_to_1(n : ℕ)(hn : n ≤ 2 * n)(gol:  2 * n - n + 1 = n + 1) :
   2 * n + 1 - n = n + 1 := by
  have two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1  := by
    rw[add_comm]
    rw[Nat.add_sub_assoc hn]
    rw[add_comm]
  rw[two_mul_add_sub]
  apply gol

theorem two_mul_succ_sub_from_0_to_2(n : ℕ)(hn : n ≤ 2 * n)(gol:  2 * n - n = n) :
   2 * n + 1 - n = n + 1 := by
  have two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1  := by
    rw[add_comm]
    rw[Nat.add_sub_assoc hn]
    rw[add_comm]
  rw[two_mul_add_sub]
  simp
  apply gol

theorem two_mul_succ_sub_from_0_to_3(n : ℕ)(hn : n ≤ 2 * n)(gol:  2 * n - n = n) :
   2 * n + 1 - n = n + 1 := by
  have two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1  := by
    rw[add_comm]
    rw[Nat.add_sub_assoc hn]
    rw[add_comm]
  rw[two_mul_add_sub]
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  apply gol

theorem two_mul_succ_sub_from_0_to_4(n : ℕ)(hn : n ≤ 2 * n)(gol:  2 * n - 1 * n = n) :
   2 * n + 1 - n = n + 1 := by
  have two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1  := by
    rw[add_comm]
    rw[Nat.add_sub_assoc hn]
    rw[add_comm]
  rw[two_mul_add_sub]
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  apply gol

theorem two_mul_succ_sub_from_0_to_5(n : ℕ)(hn : n ≤ 2 * n)(gol:  (2 - 1) * n = n) :
   2 * n + 1 - n = n + 1 := by
  have two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1  := by
    rw[add_comm]
    rw[Nat.add_sub_assoc hn]
    rw[add_comm]
  rw[two_mul_add_sub]
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  apply gol

theorem two_mul_succ_sub_from_0_to_6(n : ℕ)(hn : n ≤ 2 * n) :
   2 * n + 1 - n = n + 1 := by
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

theorem two_mul_succ_sub_from_1_to_1(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  2 * n - n + 1 = n + 1) :
   2 * n + 1 - n = n + 1 := by
  rw[two_mul_add_sub]
  apply gol

theorem two_mul_succ_sub_from_1_to_2(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  2 * n - n = n) :
   2 * n + 1 - n = n + 1 := by
  rw[two_mul_add_sub]
  simp
  apply gol

theorem two_mul_succ_sub_from_1_to_3(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  2 * n - n = n) :
   2 * n + 1 - n = n + 1 := by
  rw[two_mul_add_sub]
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  apply gol

theorem two_mul_succ_sub_from_1_to_4(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  2 * n - 1 * n = n) :
   2 * n + 1 - n = n + 1 := by
  rw[two_mul_add_sub]
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  apply gol

theorem two_mul_succ_sub_from_1_to_5(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  (2 - 1) * n = n) :
   2 * n + 1 - n = n + 1 := by
  rw[two_mul_add_sub]
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  apply gol

theorem two_mul_succ_sub_from_1_to_6(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1) :
   2 * n + 1 - n = n + 1 := by
  rw[two_mul_add_sub]
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  simp

theorem two_mul_succ_sub_from_2_to_2(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  2 * n - n = n) :
   2 * n - n + 1 = n + 1 := by
  simp
  apply gol

theorem two_mul_succ_sub_from_2_to_3(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  2 * n - n = n) :
   2 * n - n + 1 = n + 1 := by
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  apply gol

theorem two_mul_succ_sub_from_2_to_4(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  2 * n - 1 * n = n) :
   2 * n - n + 1 = n + 1 := by
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  apply gol

theorem two_mul_succ_sub_from_2_to_5(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  (2 - 1) * n = n) :
   2 * n - n + 1 = n + 1 := by
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  apply gol

theorem two_mul_succ_sub_from_2_to_6(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1) :
   2 * n - n + 1 = n + 1 := by
  simp
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  simp

theorem two_mul_succ_sub_from_3_to_3(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  2 * n - n = n) :
   2 * n - n = n := by
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  apply gol

theorem two_mul_succ_sub_from_3_to_4(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  2 * n - 1 * n = n) :
   2 * n - n = n := by
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  apply gol

theorem two_mul_succ_sub_from_3_to_5(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(gol:  (2 - 1) * n = n) :
   2 * n - n = n := by
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  apply gol

theorem two_mul_succ_sub_from_3_to_6(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1) :
   2 * n - n = n := by
  have two_mul_sub: 2 * n - n = 2 * n - 1 * n := by simp
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  simp

theorem two_mul_succ_sub_from_4_to_4(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(two_mul_sub : 2 * n - n = 2 * n - 1 * n)(gol:  2 * n - 1 * n = n) :
   2 * n - n = n := by
  rw[two_mul_sub]
  apply gol

theorem two_mul_succ_sub_from_4_to_5(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(two_mul_sub : 2 * n - n = 2 * n - 1 * n)(gol:  (2 - 1) * n = n) :
   2 * n - n = n := by
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  apply gol

theorem two_mul_succ_sub_from_4_to_6(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(two_mul_sub : 2 * n - n = 2 * n - 1 * n) :
   2 * n - n = n := by
  rw[two_mul_sub]
  rw[← Nat.mul_sub_right_distrib]
  simp

theorem two_mul_succ_sub_from_5_to_5(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(two_mul_sub : 2 * n - n = 2 * n - 1 * n)(gol:  (2 - 1) * n = n) :
   2 * n - 1 * n = n := by
  rw[← Nat.mul_sub_right_distrib]
  apply gol

theorem two_mul_succ_sub_from_5_to_6(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(two_mul_sub : 2 * n - n = 2 * n - 1 * n) :
   2 * n - 1 * n = n := by
  rw[← Nat.mul_sub_right_distrib]
  simp

theorem two_mul_succ_sub_from_6_to_6(n : ℕ)(hn : n ≤ 2 * n)(two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1)(two_mul_sub : 2 * n - n = 2 * n - 1 * n) :
   (2 - 1) * n = n := by
  simp

