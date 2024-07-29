import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


theorem inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
  rw[div_eq_mul_one_div]
  rw[mul_comm, mul_assoc]


theorem inv_2m_add_from_0_to_0(m : ℝ)(k : ℕ)(gol:  ↑k * (-1 : ℝ) ^ k * (1 / (2 * m + 1)) = 1 / (2 * m + 1) * ↑k * (-1 : ℝ) ^ k) :
   ↑k * (-1 : ℝ) ^ k / (2 * m + 1) = 1 / (2 * m + 1) * ↑k * (-1 : ℝ) ^ k := by
  rw[div_eq_mul_one_div]
  apply gol

theorem inv_2m_add_from_0_to_1(m : ℝ)(k : ℕ) :
   ↑k * (-1 : ℝ) ^ k / (2 * m + 1) = 1 / (2 * m + 1) * ↑k * (-1 : ℝ) ^ k := by
  rw[div_eq_mul_one_div]
  rw[mul_comm, mul_assoc]

theorem inv_2m_add_from_1_to_1(m : ℝ)(k : ℕ) :
   ↑k * (-1 : ℝ) ^ k * (1 / (2 * m + 1)) = 1 / (2 * m + 1) * ↑k * (-1 : ℝ) ^ k := by
  rw[mul_comm, mul_assoc]

