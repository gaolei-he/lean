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
