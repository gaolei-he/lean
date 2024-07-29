import Mathlib.Data.Real.Basic


theorem pow_neg_succ_succ{ y : ℕ }: (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + y + 1) := by
  rw[add_comm, ← add_assoc]
  norm_num
  rw[pow_add]
  simp


theorem pow_neg_succ_succ_from_0_to_0(y : ℕ)(gol:  (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + 1 + y)) :
   (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + y + 1) := by
  rw[add_comm, ← add_assoc]
  apply gol

theorem pow_neg_succ_succ_from_0_to_1(y : ℕ)(gol:  (-1 : ℝ) ^ y = (-1 : ℝ) ^ (2 + y)) :
   (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + y + 1) := by
  rw[add_comm, ← add_assoc]
  norm_num
  apply gol

theorem pow_neg_succ_succ_from_0_to_2(y : ℕ)(gol:  (-1 : ℝ) ^ y = (-1 : ℝ) ^ 2 * (-1 : ℝ) ^ y) :
   (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + y + 1) := by
  rw[add_comm, ← add_assoc]
  norm_num
  rw[pow_add]
  apply gol

theorem pow_neg_succ_succ_from_0_to_3(y : ℕ) :
   (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + y + 1) := by
  rw[add_comm, ← add_assoc]
  norm_num
  rw[pow_add]
  simp

theorem pow_neg_succ_succ_from_1_to_1(y : ℕ)(gol:  (-1 : ℝ) ^ y = (-1 : ℝ) ^ (2 + y)) :
   (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + 1 + y) := by
  norm_num
  apply gol

theorem pow_neg_succ_succ_from_1_to_2(y : ℕ)(gol:  (-1 : ℝ) ^ y = (-1 : ℝ) ^ 2 * (-1 : ℝ) ^ y) :
   (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + 1 + y) := by
  norm_num
  rw[pow_add]
  apply gol

theorem pow_neg_succ_succ_from_1_to_3(y : ℕ) :
   (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + 1 + y) := by
  norm_num
  rw[pow_add]
  simp

theorem pow_neg_succ_succ_from_2_to_2(y : ℕ)(gol:  (-1 : ℝ) ^ y = (-1 : ℝ) ^ 2 * (-1 : ℝ) ^ y) :
   (-1 : ℝ) ^ y = (-1 : ℝ) ^ (2 + y) := by
  rw[pow_add]
  apply gol

theorem pow_neg_succ_succ_from_2_to_3(y : ℕ) :
   (-1 : ℝ) ^ y = (-1 : ℝ) ^ (2 + y) := by
  rw[pow_add]
  simp

theorem pow_neg_succ_succ_from_3_to_3(y : ℕ) :
   (-1 : ℝ) ^ y = (-1 : ℝ) ^ 2 * (-1 : ℝ) ^ y := by
  simp

