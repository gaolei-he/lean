import Mathlib.Data.Real.Basic


theorem mul_two_div_mul(hnm: n = 2 * m): (2 * (m : ℝ) + 1) / (((m : ℝ) + 1)) * (1/2) = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1/2) := by
  rw[← div_eq_mul_one_div]
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  rw[hnm]



theorem mul_two_div_mul_from_0_to_0(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (m + 1) / 2 = 2 * (n + 1) / (n + 2) * (1 / 2)) :
   (2 * m + 1) / (m + 1) * (1 / 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[← div_eq_mul_one_div]
  apply gol

theorem mul_two_div_mul_from_0_to_1(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / ((m + 1) * 2) = 2 * (n + 1) / (n + 2) * (1 / 2)) :
   (2 * m + 1) / (m + 1) * (1 / 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[← div_eq_mul_one_div]
  rw[div_div]
  apply gol

theorem mul_two_div_mul_from_0_to_2(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 1 * 2) = 2 * (n + 1) / (n + 2) * (1 / 2)) :
   (2 * m + 1) / (m + 1) * (1 / 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[← div_eq_mul_one_div]
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  apply gol

theorem mul_two_div_mul_from_0_to_3(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * (n + 1) / (n + 2) * 2⁻¹) :
   (2 * m + 1) / (m + 1) * (1 / 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[← div_eq_mul_one_div]
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  apply gol

theorem mul_two_div_mul_from_0_to_4(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * ((n + 1) / (n + 2)) * 2⁻¹) :
   (2 * m + 1) / (m + 1) * (1 / 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[← div_eq_mul_one_div]
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  apply gol

theorem mul_two_div_mul_from_0_to_5(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * 2⁻¹ * ((n + 1) / (n + 2))) :
   (2 * m + 1) / (m + 1) * (1 / 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[← div_eq_mul_one_div]
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  apply gol

theorem mul_two_div_mul_from_0_to_6(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = (n + 1) / (n + 2)) :
   (2 * m + 1) / (m + 1) * (1 / 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[← div_eq_mul_one_div]
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  apply gol

theorem mul_two_div_mul_from_0_to_7(n m : ℝ)(hnm : n = 2 * m) :
   (2 * m + 1) / (m + 1) * (1 / 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[← div_eq_mul_one_div]
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  rw[hnm]

theorem mul_two_div_mul_from_1_to_1(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / ((m + 1) * 2) = 2 * (n + 1) / (n + 2) * (1 / 2)) :
   (2 * m + 1) / (m + 1) / 2 = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[div_div]
  apply gol

theorem mul_two_div_mul_from_1_to_2(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 1 * 2) = 2 * (n + 1) / (n + 2) * (1 / 2)) :
   (2 * m + 1) / (m + 1) / 2 = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  apply gol

theorem mul_two_div_mul_from_1_to_3(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * (n + 1) / (n + 2) * 2⁻¹) :
   (2 * m + 1) / (m + 1) / 2 = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  apply gol

theorem mul_two_div_mul_from_1_to_4(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * ((n + 1) / (n + 2)) * 2⁻¹) :
   (2 * m + 1) / (m + 1) / 2 = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  apply gol

theorem mul_two_div_mul_from_1_to_5(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * 2⁻¹ * ((n + 1) / (n + 2))) :
   (2 * m + 1) / (m + 1) / 2 = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  apply gol

theorem mul_two_div_mul_from_1_to_6(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = (n + 1) / (n + 2)) :
   (2 * m + 1) / (m + 1) / 2 = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  apply gol

theorem mul_two_div_mul_from_1_to_7(n m : ℝ)(hnm : n = 2 * m) :
   (2 * m + 1) / (m + 1) / 2 = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[div_div]
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  rw[hnm]

theorem mul_two_div_mul_from_2_to_2(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 1 * 2) = 2 * (n + 1) / (n + 2) * (1 / 2)) :
   (2 * m + 1) / ((m + 1) * 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[add_mul, mul_comm (m : ℝ) 2]
  apply gol

theorem mul_two_div_mul_from_2_to_3(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * (n + 1) / (n + 2) * 2⁻¹) :
   (2 * m + 1) / ((m + 1) * 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  apply gol

theorem mul_two_div_mul_from_2_to_4(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * ((n + 1) / (n + 2)) * 2⁻¹) :
   (2 * m + 1) / ((m + 1) * 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  apply gol

theorem mul_two_div_mul_from_2_to_5(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * 2⁻¹ * ((n + 1) / (n + 2))) :
   (2 * m + 1) / ((m + 1) * 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  apply gol

theorem mul_two_div_mul_from_2_to_6(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = (n + 1) / (n + 2)) :
   (2 * m + 1) / ((m + 1) * 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  apply gol

theorem mul_two_div_mul_from_2_to_7(n m : ℝ)(hnm : n = 2 * m) :
   (2 * m + 1) / ((m + 1) * 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  rw[add_mul, mul_comm (m : ℝ) 2]
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  rw[hnm]

theorem mul_two_div_mul_from_3_to_3(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * (n + 1) / (n + 2) * 2⁻¹) :
   (2 * m + 1) / (2 * m + 1 * 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  simp
  apply gol

theorem mul_two_div_mul_from_3_to_4(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * ((n + 1) / (n + 2)) * 2⁻¹) :
   (2 * m + 1) / (2 * m + 1 * 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  simp
  rw[← mul_div]
  apply gol

theorem mul_two_div_mul_from_3_to_5(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * 2⁻¹ * ((n + 1) / (n + 2))) :
   (2 * m + 1) / (2 * m + 1 * 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  apply gol

theorem mul_two_div_mul_from_3_to_6(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = (n + 1) / (n + 2)) :
   (2 * m + 1) / (2 * m + 1 * 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  apply gol

theorem mul_two_div_mul_from_3_to_7(n m : ℝ)(hnm : n = 2 * m) :
   (2 * m + 1) / (2 * m + 1 * 2) = 2 * (n + 1) / (n + 2) * (1 / 2) := by
  simp
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  rw[hnm]

theorem mul_two_div_mul_from_4_to_4(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * ((n + 1) / (n + 2)) * 2⁻¹) :
   (2 * m + 1) / (2 * m + 2) = 2 * (n + 1) / (n + 2) * 2⁻¹ := by
  rw[← mul_div]
  apply gol

theorem mul_two_div_mul_from_4_to_5(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * 2⁻¹ * ((n + 1) / (n + 2))) :
   (2 * m + 1) / (2 * m + 2) = 2 * (n + 1) / (n + 2) * 2⁻¹ := by
  rw[← mul_div]
  rw[mul_right_comm]
  apply gol

theorem mul_two_div_mul_from_4_to_6(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = (n + 1) / (n + 2)) :
   (2 * m + 1) / (2 * m + 2) = 2 * (n + 1) / (n + 2) * 2⁻¹ := by
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  apply gol

theorem mul_two_div_mul_from_4_to_7(n m : ℝ)(hnm : n = 2 * m) :
   (2 * m + 1) / (2 * m + 2) = 2 * (n + 1) / (n + 2) * 2⁻¹ := by
  rw[← mul_div]
  rw[mul_right_comm]
  simp
  rw[hnm]

theorem mul_two_div_mul_from_5_to_5(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = 2 * 2⁻¹ * ((n + 1) / (n + 2))) :
   (2 * m + 1) / (2 * m + 2) = 2 * ((n + 1) / (n + 2)) * 2⁻¹ := by
  rw[mul_right_comm]
  apply gol

theorem mul_two_div_mul_from_5_to_6(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = (n + 1) / (n + 2)) :
   (2 * m + 1) / (2 * m + 2) = 2 * ((n + 1) / (n + 2)) * 2⁻¹ := by
  rw[mul_right_comm]
  simp
  apply gol

theorem mul_two_div_mul_from_5_to_7(n m : ℝ)(hnm : n = 2 * m) :
   (2 * m + 1) / (2 * m + 2) = 2 * ((n + 1) / (n + 2)) * 2⁻¹ := by
  rw[mul_right_comm]
  simp
  rw[hnm]

theorem mul_two_div_mul_from_6_to_6(n m : ℝ)(hnm : n = 2 * m)(gol:  (2 * m + 1) / (2 * m + 2) = (n + 1) / (n + 2)) :
   (2 * m + 1) / (2 * m + 2) = 2 * 2⁻¹ * ((n + 1) / (n + 2)) := by
  simp
  apply gol

theorem mul_two_div_mul_from_6_to_7(n m : ℝ)(hnm : n = 2 * m) :
   (2 * m + 1) / (2 * m + 2) = 2 * 2⁻¹ * ((n + 1) / (n + 2)) := by
  simp
  rw[hnm]

theorem mul_two_div_mul_from_7_to_7(n m : ℝ)(hnm : n = 2 * m) :
   (2 * m + 1) / (2 * m + 2) = (n + 1) / (n + 2) := by
  rw[hnm]

