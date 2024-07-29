import Mathlib.Data.Real.Basic


theorem two_mul_div_add{m : ℕ }(hm : 0 < m) : 2 * (m + 1) / (m + 1)  + (-1 : ℝ) / (m + 1) = 2 + (-1 : ℝ) / (m + 1) := by
    congr 1
    rw[mul_div_assoc]
    simp
    have m_r : 0 < (m : ℝ) := by
      simp
      exact hm
    have hm_z : (m : ℝ) + 1 ≠ 0  := by
      linarith
    rw[div_self hm_z]


theorem two_mul_div_add_from_1_to_1(m : ℕ)(hm : 0 < m)(gol:  2 * ((↑m + 1) / (↑m + 1)) = 2) :
   2 * (↑m + 1) / (↑m + 1) = 2 := by
  rw[mul_div_assoc]
  apply gol

theorem two_mul_div_add_from_1_to_2(m : ℕ)(hm : 0 < m)(gol:  (↑m + 1) / (↑m + 1) = 1) :
   2 * (↑m + 1) / (↑m + 1) = 2 := by
  rw[mul_div_assoc]
  simp
  apply gol

theorem two_mul_div_add_from_1_to_3(m : ℕ)(hm : 0 < m)(gol:  (↑m + 1) / (↑m + 1) = 1) :
   2 * (↑m + 1) / (↑m + 1) = 2 := by
  rw[mul_div_assoc]
  simp
  have m_r : 0 < (m : ℝ) := by
    simp
    exact hm
  apply gol

theorem two_mul_div_add_from_1_to_4(m : ℕ)(hm : 0 < m)(gol:  (↑m + 1) / (↑m + 1) = 1) :
   2 * (↑m + 1) / (↑m + 1) = 2 := by
  rw[mul_div_assoc]
  simp
  have m_r : 0 < (m : ℝ) := by
    simp
    exact hm
  have hm_z : (m : ℝ) + 1 ≠ 0  := by
    linarith
  apply gol

theorem two_mul_div_add_from_1_to_5(m : ℕ)(hm : 0 < m) :
   2 * (↑m + 1) / (↑m + 1) = 2 := by
  rw[mul_div_assoc]
  simp
  have m_r : 0 < (m : ℝ) := by
    simp
    exact hm
  have hm_z : (m : ℝ) + 1 ≠ 0  := by
    linarith
  rw[div_self hm_z]

theorem two_mul_div_add_from_2_to_2(m : ℕ)(hm : 0 < m)(gol:  (↑m + 1) / (↑m + 1) = 1) :
   2 * ((↑m + 1) / (↑m + 1)) = 2 := by
  simp
  apply gol

theorem two_mul_div_add_from_2_to_3(m : ℕ)(hm : 0 < m)(gol:  (↑m + 1) / (↑m + 1) = 1) :
   2 * ((↑m + 1) / (↑m + 1)) = 2 := by
  simp
  have m_r : 0 < (m : ℝ) := by
    simp
    exact hm
  apply gol

theorem two_mul_div_add_from_2_to_4(m : ℕ)(hm : 0 < m)(gol:  (↑m + 1) / (↑m + 1) = 1) :
   2 * ((↑m + 1) / (↑m + 1)) = 2 := by
  simp
  have m_r : 0 < (m : ℝ) := by
    simp
    exact hm
  have hm_z : (m : ℝ) + 1 ≠ 0  := by
    linarith
  apply gol

theorem two_mul_div_add_from_2_to_5(m : ℕ)(hm : 0 < m) :
   2 * ((↑m + 1) / (↑m + 1)) = 2 := by
  simp
  have m_r : 0 < (m : ℝ) := by
    simp
    exact hm
  have hm_z : (m : ℝ) + 1 ≠ 0  := by
    linarith
  rw[div_self hm_z]

theorem two_mul_div_add_from_3_to_3(m : ℕ)(hm : 0 < m)(gol:  (↑m + 1) / (↑m + 1) = 1) :
   (↑m + 1) / (↑m + 1) = 1 := by
  have m_r : 0 < (m : ℝ) := by
    simp
    exact hm
  apply gol

theorem two_mul_div_add_from_3_to_4(m : ℕ)(hm : 0 < m)(gol:  (↑m + 1) / (↑m + 1) = 1) :
   (↑m + 1) / (↑m + 1) = 1 := by
  have m_r : 0 < (m : ℝ) := by
    simp
    exact hm
  have hm_z : (m : ℝ) + 1 ≠ 0  := by
    linarith
  apply gol

theorem two_mul_div_add_from_3_to_5(m : ℕ)(hm : 0 < m) :
   (↑m + 1) / (↑m + 1) = 1 := by
  have m_r : 0 < (m : ℝ) := by
    simp
    exact hm
  have hm_z : (m : ℝ) + 1 ≠ 0  := by
    linarith
  rw[div_self hm_z]

theorem two_mul_div_add_from_4_to_4(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(gol:  (↑m + 1) / (↑m + 1) = 1) :
   (↑m + 1) / (↑m + 1) = 1 := by
  have hm_z : (m : ℝ) + 1 ≠ 0  := by
    linarith
  apply gol

theorem two_mul_div_add_from_4_to_5(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m) :
   (↑m + 1) / (↑m + 1) = 1 := by
  have hm_z : (m : ℝ) + 1 ≠ 0  := by
    linarith
  rw[div_self hm_z]

theorem two_mul_div_add_from_5_to_5(m : ℕ)(hm : 0 < m)(m_r : 0 < ↑m)(hm_z : ↑m + 1 ≠ 0) :
   (↑m + 1) / (↑m + 1) = 1 := by
  rw[div_self hm_z]

