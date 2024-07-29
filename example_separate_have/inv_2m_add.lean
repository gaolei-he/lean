import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


theorem inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
  rw[div_eq_mul_one_div]
  rw[mul_comm, mul_assoc]
