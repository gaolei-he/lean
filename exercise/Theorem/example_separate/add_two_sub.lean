import Mathlib.Data.Nat.Choose.Sum


theorem add_two_sub: 2 * n + 1 - n = n + 1 := by
 rw[two_mul]
 rw[add_assoc]
 rw[add_comm]
 simp


theorem add_two_sub_from_0_to_0(n : ℕ)(gol:  n + n + 1 - n = n + 1) :
   2 * n + 1 - n = n + 1 := by
  rw[two_mul]
  apply gol

theorem add_two_sub_from_0_to_1(n : ℕ)(gol:  n + (n + 1) - n = n + 1) :
   2 * n + 1 - n = n + 1 := by
  rw[two_mul]
  rw[add_assoc]
  apply gol

theorem add_two_sub_from_0_to_2(n : ℕ)(gol:  n + 1 + n - n = n + 1) :
   2 * n + 1 - n = n + 1 := by
  rw[two_mul]
  rw[add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_sub_from_0_to_3(n : ℕ) :
   2 * n + 1 - n = n + 1 := by
  rw[two_mul]
  rw[add_assoc]
  rw[add_comm]
  simp

theorem add_two_sub_from_1_to_1(n : ℕ)(gol:  n + (n + 1) - n = n + 1) :
   n + n + 1 - n = n + 1 := by
  rw[add_assoc]
  apply gol

theorem add_two_sub_from_1_to_2(n : ℕ)(gol:  n + 1 + n - n = n + 1) :
   n + n + 1 - n = n + 1 := by
  rw[add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_sub_from_1_to_3(n : ℕ) :
   n + n + 1 - n = n + 1 := by
  rw[add_assoc]
  rw[add_comm]
  simp

theorem add_two_sub_from_2_to_2(n : ℕ)(gol:  n + 1 + n - n = n + 1) :
   n + (n + 1) - n = n + 1 := by
  rw[add_comm]
  apply gol

theorem add_two_sub_from_2_to_3(n : ℕ) :
   n + (n + 1) - n = n + 1 := by
  rw[add_comm]
  simp

theorem add_two_sub_from_3_to_3(n : ℕ) :
   n + 1 + n - n = n + 1 := by
  simp

