import Mathlib.Data.Real.Basic


theorem add_neg_div {m : ℕ }(hm : 0 < m): 2 + (-1 : ℝ) / (m + 1) = (2 * m + 1) / (m + 1) := by   -- 第四个等式
  have m_r : 0 < (m : ℝ) := by
      simp
      exact hm
  have hm_z : (m : ℝ) + 1 ≠ 0  := by
      linarith
  have two_m_div_add : 2 * (m + 1) / (m + 1)  + (-1 : ℝ) / (m + 1) = 2 + (-1 : ℝ) / (m + 1) := by
    congr 1
    rw[mul_div_assoc]
    simp
    rw[div_self hm_z]
  rw[← two_m_div_add]
  rw[div_add_div_same]  -- 除法分配律
  rw[mul_comm, add_mul]
  rw[add_assoc]
  norm_num
  rw[mul_comm]


theorem add_neg_div_from_0_to_0(m : ℕ)(hm : 0 < m)(gol:  2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  have m_r : 0 < (m : ℝ) := by
      simp
      exact hm
  apply gol

theorem add_neg_div_from_0_to_1(m : ℕ)(hm : 0 < m)(gol:  2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  have m_r : 0 < (m : ℝ) := by
      simp
      exact hm
  have hm_z : (m : ℝ) + 1 ≠ 0  := by
      linarith
  apply gol

theorem add_neg_div_from_1_to_1(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(gol:  2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  have hm_z : (m : ℝ) + 1 ≠ 0  := by
      linarith
  apply gol

theorem add_neg_div_from_3_to_3(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[← two_m_div_add]
  apply gol

theorem add_neg_div_from_3_to_4(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (2 * (↑m + 1) + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[← two_m_div_add]
  rw[div_add_div_same]
  apply gol

theorem add_neg_div_from_3_to_5(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + 1 * 2 + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[← two_m_div_add]
  rw[div_add_div_same]
  rw[mul_comm, add_mul]
  apply gol

theorem add_neg_div_from_3_to_6(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + (1 * 2 + -1)) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[← two_m_div_add]
  rw[div_add_div_same]
  rw[mul_comm, add_mul]
  rw[add_assoc]
  apply gol

theorem add_neg_div_from_3_to_7(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + 1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[← two_m_div_add]
  rw[div_add_div_same]
  rw[mul_comm, add_mul]
  rw[add_assoc]
  norm_num
  apply gol

theorem add_neg_div_from_3_to_8(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1)) :
   2 + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[← two_m_div_add]
  rw[div_add_div_same]
  rw[mul_comm, add_mul]
  rw[add_assoc]
  norm_num
  rw[mul_comm]

theorem add_neg_div_from_4_to_4(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (2 * (↑m + 1) + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[div_add_div_same]
  apply gol

theorem add_neg_div_from_4_to_5(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + 1 * 2 + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[div_add_div_same]
  rw[mul_comm, add_mul]
  apply gol

theorem add_neg_div_from_4_to_6(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + (1 * 2 + -1)) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[div_add_div_same]
  rw[mul_comm, add_mul]
  rw[add_assoc]
  apply gol

theorem add_neg_div_from_4_to_7(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + 1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[div_add_div_same]
  rw[mul_comm, add_mul]
  rw[add_assoc]
  norm_num
  apply gol

theorem add_neg_div_from_4_to_8(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1)) :
   2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[div_add_div_same]
  rw[mul_comm, add_mul]
  rw[add_assoc]
  norm_num
  rw[mul_comm]

theorem add_neg_div_from_5_to_5(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + 1 * 2 + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   (2 * (↑m + 1) + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[mul_comm, add_mul]
  apply gol

theorem add_neg_div_from_5_to_6(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + (1 * 2 + -1)) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   (2 * (↑m + 1) + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[mul_comm, add_mul]
  rw[add_assoc]
  apply gol

theorem add_neg_div_from_5_to_7(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + 1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   (2 * (↑m + 1) + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[mul_comm, add_mul]
  rw[add_assoc]
  norm_num
  apply gol

theorem add_neg_div_from_5_to_8(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1)) :
   (2 * (↑m + 1) + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[mul_comm, add_mul]
  rw[add_assoc]
  norm_num
  rw[mul_comm]

theorem add_neg_div_from_6_to_6(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + (1 * 2 + -1)) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   (↑m * 2 + 1 * 2 + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[add_assoc]
  apply gol

theorem add_neg_div_from_6_to_7(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + 1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   (↑m * 2 + 1 * 2 + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[add_assoc]
  norm_num
  apply gol

theorem add_neg_div_from_6_to_8(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1)) :
   (↑m * 2 + 1 * 2 + -1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[add_assoc]
  norm_num
  rw[mul_comm]

theorem add_neg_div_from_7_to_7(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1))(gol:  (↑m * 2 + 1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1)) :
   (↑m * 2 + (1 * 2 + -1)) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  norm_num
  apply gol

theorem add_neg_div_from_7_to_8(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1)) :
   (↑m * 2 + (1 * 2 + -1)) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  norm_num
  rw[mul_comm]

theorem add_neg_div_from_8_to_8(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0)(two_m_div_add : 2 * (↑m + 1) / (↑m + 1) + -1 / (↑m + 1) = 2 + -1 / (↑m + 1)) :
   (↑m * 2 + 1) / (↑m + 1) = (2 * ↑m + 1) / (↑m + 1) := by
  rw[mul_comm]

