import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators


theorem add_two_subY(n y : ℕ): n - (2 * n - y) =(-1:ℝ)*(n - y) := by
 simp
 rw[two_mul]
 rw[sub_eq_neg_add]
 rw[neg_sub]
 rw[sub_eq_neg_add]
 rw[neg_add]
 rw[sub_eq_neg_add]
 rw[add_assoc]
 rw[add_comm]
 rw[← add_assoc]
 rw[add_comm]
 congr 1
 rw[add_assoc]
 simp


theorem add_two_subY_from_0_to_0(n y : ℕ)(gol:  ↑n - (2 * ↑n - ↑y) = ↑y - ↑n) :
   ↑n - (2 * ↑n - ↑y) = -1 * (↑n - ↑y) := by
  simp
  apply gol

theorem add_two_subY_from_0_to_1(n y : ℕ)(gol:  ↑n - (↑n + ↑n - ↑y) = ↑y - ↑n) :
   ↑n - (2 * ↑n - ↑y) = -1 * (↑n - ↑y) := by
  simp
  rw[two_mul]
  apply gol

theorem add_two_subY_from_0_to_2(n y : ℕ)(gol:  -(↑n + ↑n - ↑y) + ↑n = ↑y - ↑n) :
   ↑n - (2 * ↑n - ↑y) = -1 * (↑n - ↑y) := by
  simp
  rw[two_mul]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_0_to_3(n y : ℕ)(gol:  ↑y - (↑n + ↑n) + ↑n = ↑y - ↑n) :
   ↑n - (2 * ↑n - ↑y) = -1 * (↑n - ↑y) := by
  simp
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  apply gol

theorem add_two_subY_from_0_to_4(n y : ℕ)(gol:  -(↑n + ↑n) + ↑y + ↑n = ↑y - ↑n) :
   ↑n - (2 * ↑n - ↑y) = -1 * (↑n - ↑y) := by
  simp
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_0_to_5(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = ↑y - ↑n) :
   ↑n - (2 * ↑n - ↑y) = -1 * (↑n - ↑y) := by
  simp
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  apply gol

theorem add_two_subY_from_0_to_6(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = -↑n + ↑y) :
   ↑n - (2 * ↑n - ↑y) = -1 * (↑n - ↑y) := by
  simp
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_0_to_7(n y : ℕ)(gol:  -↑n + -↑n + (↑y + ↑n) = -↑n + ↑y) :
   ↑n - (2 * ↑n - ↑y) = -1 * (↑n - ↑y) := by
  simp
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  apply gol

theorem add_two_subY_from_0_to_8(n y : ℕ)(gol:  ↑y + ↑n + (-↑n + -↑n) = -↑n + ↑y) :
   ↑n - (2 * ↑n - ↑y) = -1 * (↑n - ↑y) := by
  simp
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_0_to_9(n y : ℕ)(gol:  ↑y + ↑n + -↑n + -↑n = -↑n + ↑y) :
   ↑n - (2 * ↑n - ↑y) = -1 * (↑n - ↑y) := by
  simp
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  apply gol

theorem add_two_subY_from_0_to_10(n y : ℕ)(gol:  -↑n + (↑y + ↑n + -↑n) = -↑n + ↑y) :
   ↑n - (2 * ↑n - ↑y) = -1 * (↑n - ↑y) := by
  simp
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_1_to_1(n y : ℕ)(gol:  ↑n - (↑n + ↑n - ↑y) = ↑y - ↑n) :
   ↑n - (2 * ↑n - ↑y) = ↑y - ↑n := by
  rw[two_mul]
  apply gol

theorem add_two_subY_from_1_to_2(n y : ℕ)(gol:  -(↑n + ↑n - ↑y) + ↑n = ↑y - ↑n) :
   ↑n - (2 * ↑n - ↑y) = ↑y - ↑n := by
  rw[two_mul]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_1_to_3(n y : ℕ)(gol:  ↑y - (↑n + ↑n) + ↑n = ↑y - ↑n) :
   ↑n - (2 * ↑n - ↑y) = ↑y - ↑n := by
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  apply gol

theorem add_two_subY_from_1_to_4(n y : ℕ)(gol:  -(↑n + ↑n) + ↑y + ↑n = ↑y - ↑n) :
   ↑n - (2 * ↑n - ↑y) = ↑y - ↑n := by
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_1_to_5(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = ↑y - ↑n) :
   ↑n - (2 * ↑n - ↑y) = ↑y - ↑n := by
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  apply gol

theorem add_two_subY_from_1_to_6(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = -↑n + ↑y) :
   ↑n - (2 * ↑n - ↑y) = ↑y - ↑n := by
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_1_to_7(n y : ℕ)(gol:  -↑n + -↑n + (↑y + ↑n) = -↑n + ↑y) :
   ↑n - (2 * ↑n - ↑y) = ↑y - ↑n := by
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  apply gol

theorem add_two_subY_from_1_to_8(n y : ℕ)(gol:  ↑y + ↑n + (-↑n + -↑n) = -↑n + ↑y) :
   ↑n - (2 * ↑n - ↑y) = ↑y - ↑n := by
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_1_to_9(n y : ℕ)(gol:  ↑y + ↑n + -↑n + -↑n = -↑n + ↑y) :
   ↑n - (2 * ↑n - ↑y) = ↑y - ↑n := by
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  apply gol

theorem add_two_subY_from_1_to_10(n y : ℕ)(gol:  -↑n + (↑y + ↑n + -↑n) = -↑n + ↑y) :
   ↑n - (2 * ↑n - ↑y) = ↑y - ↑n := by
  rw[two_mul]
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_2_to_2(n y : ℕ)(gol:  -(↑n + ↑n - ↑y) + ↑n = ↑y - ↑n) :
   ↑n - (↑n + ↑n - ↑y) = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_2_to_3(n y : ℕ)(gol:  ↑y - (↑n + ↑n) + ↑n = ↑y - ↑n) :
   ↑n - (↑n + ↑n - ↑y) = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_sub]
  apply gol

theorem add_two_subY_from_2_to_4(n y : ℕ)(gol:  -(↑n + ↑n) + ↑y + ↑n = ↑y - ↑n) :
   ↑n - (↑n + ↑n - ↑y) = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_2_to_5(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = ↑y - ↑n) :
   ↑n - (↑n + ↑n - ↑y) = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  apply gol

theorem add_two_subY_from_2_to_6(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = -↑n + ↑y) :
   ↑n - (↑n + ↑n - ↑y) = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_2_to_7(n y : ℕ)(gol:  -↑n + -↑n + (↑y + ↑n) = -↑n + ↑y) :
   ↑n - (↑n + ↑n - ↑y) = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  apply gol

theorem add_two_subY_from_2_to_8(n y : ℕ)(gol:  ↑y + ↑n + (-↑n + -↑n) = -↑n + ↑y) :
   ↑n - (↑n + ↑n - ↑y) = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_2_to_9(n y : ℕ)(gol:  ↑y + ↑n + -↑n + -↑n = -↑n + ↑y) :
   ↑n - (↑n + ↑n - ↑y) = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  apply gol

theorem add_two_subY_from_2_to_10(n y : ℕ)(gol:  -↑n + (↑y + ↑n + -↑n) = -↑n + ↑y) :
   ↑n - (↑n + ↑n - ↑y) = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_3_to_3(n y : ℕ)(gol:  ↑y - (↑n + ↑n) + ↑n = ↑y - ↑n) :
   -(↑n + ↑n - ↑y) + ↑n = ↑y - ↑n := by
  rw[neg_sub]
  apply gol

theorem add_two_subY_from_3_to_4(n y : ℕ)(gol:  -(↑n + ↑n) + ↑y + ↑n = ↑y - ↑n) :
   -(↑n + ↑n - ↑y) + ↑n = ↑y - ↑n := by
  rw[neg_sub]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_3_to_5(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = ↑y - ↑n) :
   -(↑n + ↑n - ↑y) + ↑n = ↑y - ↑n := by
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  apply gol

theorem add_two_subY_from_3_to_6(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = -↑n + ↑y) :
   -(↑n + ↑n - ↑y) + ↑n = ↑y - ↑n := by
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_3_to_7(n y : ℕ)(gol:  -↑n + -↑n + (↑y + ↑n) = -↑n + ↑y) :
   -(↑n + ↑n - ↑y) + ↑n = ↑y - ↑n := by
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  apply gol

theorem add_two_subY_from_3_to_8(n y : ℕ)(gol:  ↑y + ↑n + (-↑n + -↑n) = -↑n + ↑y) :
   -(↑n + ↑n - ↑y) + ↑n = ↑y - ↑n := by
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_3_to_9(n y : ℕ)(gol:  ↑y + ↑n + -↑n + -↑n = -↑n + ↑y) :
   -(↑n + ↑n - ↑y) + ↑n = ↑y - ↑n := by
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  apply gol

theorem add_two_subY_from_3_to_10(n y : ℕ)(gol:  -↑n + (↑y + ↑n + -↑n) = -↑n + ↑y) :
   -(↑n + ↑n - ↑y) + ↑n = ↑y - ↑n := by
  rw[neg_sub]
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_4_to_4(n y : ℕ)(gol:  -(↑n + ↑n) + ↑y + ↑n = ↑y - ↑n) :
   ↑y - (↑n + ↑n) + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_4_to_5(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = ↑y - ↑n) :
   ↑y - (↑n + ↑n) + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_add]
  apply gol

theorem add_two_subY_from_4_to_6(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = -↑n + ↑y) :
   ↑y - (↑n + ↑n) + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_4_to_7(n y : ℕ)(gol:  -↑n + -↑n + (↑y + ↑n) = -↑n + ↑y) :
   ↑y - (↑n + ↑n) + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  apply gol

theorem add_two_subY_from_4_to_8(n y : ℕ)(gol:  ↑y + ↑n + (-↑n + -↑n) = -↑n + ↑y) :
   ↑y - (↑n + ↑n) + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_4_to_9(n y : ℕ)(gol:  ↑y + ↑n + -↑n + -↑n = -↑n + ↑y) :
   ↑y - (↑n + ↑n) + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  apply gol

theorem add_two_subY_from_4_to_10(n y : ℕ)(gol:  -↑n + (↑y + ↑n + -↑n) = -↑n + ↑y) :
   ↑y - (↑n + ↑n) + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_5_to_5(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = ↑y - ↑n) :
   -(↑n + ↑n) + ↑y + ↑n = ↑y - ↑n := by
  rw[neg_add]
  apply gol

theorem add_two_subY_from_5_to_6(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = -↑n + ↑y) :
   -(↑n + ↑n) + ↑y + ↑n = ↑y - ↑n := by
  rw[neg_add]
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_5_to_7(n y : ℕ)(gol:  -↑n + -↑n + (↑y + ↑n) = -↑n + ↑y) :
   -(↑n + ↑n) + ↑y + ↑n = ↑y - ↑n := by
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  apply gol

theorem add_two_subY_from_5_to_8(n y : ℕ)(gol:  ↑y + ↑n + (-↑n + -↑n) = -↑n + ↑y) :
   -(↑n + ↑n) + ↑y + ↑n = ↑y - ↑n := by
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_5_to_9(n y : ℕ)(gol:  ↑y + ↑n + -↑n + -↑n = -↑n + ↑y) :
   -(↑n + ↑n) + ↑y + ↑n = ↑y - ↑n := by
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  apply gol

theorem add_two_subY_from_5_to_10(n y : ℕ)(gol:  -↑n + (↑y + ↑n + -↑n) = -↑n + ↑y) :
   -(↑n + ↑n) + ↑y + ↑n = ↑y - ↑n := by
  rw[neg_add]
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_6_to_6(n y : ℕ)(gol:  -↑n + -↑n + ↑y + ↑n = -↑n + ↑y) :
   -↑n + -↑n + ↑y + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  apply gol

theorem add_two_subY_from_6_to_7(n y : ℕ)(gol:  -↑n + -↑n + (↑y + ↑n) = -↑n + ↑y) :
   -↑n + -↑n + ↑y + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[add_assoc]
  apply gol

theorem add_two_subY_from_6_to_8(n y : ℕ)(gol:  ↑y + ↑n + (-↑n + -↑n) = -↑n + ↑y) :
   -↑n + -↑n + ↑y + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_6_to_9(n y : ℕ)(gol:  ↑y + ↑n + -↑n + -↑n = -↑n + ↑y) :
   -↑n + -↑n + ↑y + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  apply gol

theorem add_two_subY_from_6_to_10(n y : ℕ)(gol:  -↑n + (↑y + ↑n + -↑n) = -↑n + ↑y) :
   -↑n + -↑n + ↑y + ↑n = ↑y - ↑n := by
  rw[sub_eq_neg_add]
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_7_to_7(n y : ℕ)(gol:  -↑n + -↑n + (↑y + ↑n) = -↑n + ↑y) :
   -↑n + -↑n + ↑y + ↑n = -↑n + ↑y := by
  rw[add_assoc]
  apply gol

theorem add_two_subY_from_7_to_8(n y : ℕ)(gol:  ↑y + ↑n + (-↑n + -↑n) = -↑n + ↑y) :
   -↑n + -↑n + ↑y + ↑n = -↑n + ↑y := by
  rw[add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_7_to_9(n y : ℕ)(gol:  ↑y + ↑n + -↑n + -↑n = -↑n + ↑y) :
   -↑n + -↑n + ↑y + ↑n = -↑n + ↑y := by
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  apply gol

theorem add_two_subY_from_7_to_10(n y : ℕ)(gol:  -↑n + (↑y + ↑n + -↑n) = -↑n + ↑y) :
   -↑n + -↑n + ↑y + ↑n = -↑n + ↑y := by
  rw[add_assoc]
  rw[add_comm]
  rw[← add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_8_to_8(n y : ℕ)(gol:  ↑y + ↑n + (-↑n + -↑n) = -↑n + ↑y) :
   -↑n + -↑n + (↑y + ↑n) = -↑n + ↑y := by
  rw[add_comm]
  apply gol

theorem add_two_subY_from_8_to_9(n y : ℕ)(gol:  ↑y + ↑n + -↑n + -↑n = -↑n + ↑y) :
   -↑n + -↑n + (↑y + ↑n) = -↑n + ↑y := by
  rw[add_comm]
  rw[← add_assoc]
  apply gol

theorem add_two_subY_from_8_to_10(n y : ℕ)(gol:  -↑n + (↑y + ↑n + -↑n) = -↑n + ↑y) :
   -↑n + -↑n + (↑y + ↑n) = -↑n + ↑y := by
  rw[add_comm]
  rw[← add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_9_to_9(n y : ℕ)(gol:  ↑y + ↑n + -↑n + -↑n = -↑n + ↑y) :
   ↑y + ↑n + (-↑n + -↑n) = -↑n + ↑y := by
  rw[← add_assoc]
  apply gol

theorem add_two_subY_from_9_to_10(n y : ℕ)(gol:  -↑n + (↑y + ↑n + -↑n) = -↑n + ↑y) :
   ↑y + ↑n + (-↑n + -↑n) = -↑n + ↑y := by
  rw[← add_assoc]
  rw[add_comm]
  apply gol

theorem add_two_subY_from_10_to_10(n y : ℕ)(gol:  -↑n + (↑y + ↑n + -↑n) = -↑n + ↑y) :
   ↑y + ↑n + -↑n + -↑n = -↑n + ↑y := by
  rw[add_comm]
  apply gol

theorem add_two_subY_from_12_to_12(n y : ℕ)(gol:  ↑y + (↑n + -↑n) = ↑y) :
   ↑y + ↑n + -↑n = ↑y := by
  rw[add_assoc]
  apply gol

theorem add_two_subY_from_12_to_13(n y : ℕ) :
   ↑y + ↑n + -↑n = ↑y := by
  rw[add_assoc]
  simp

theorem add_two_subY_from_13_to_13(n y : ℕ) :
   ↑y + (↑n + -↑n) = ↑y := by
  simp

