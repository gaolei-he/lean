import Mathlib.Data.Real.Basic
import AdaLean.two_m_div_add


theorem add_neg_div {m : ℕ}(hm : 0 < m): 2 + (-1 : ℝ) / (m + 1) = (2 * m + 1) / (m + 1) := by
  rw[← two_m_div_add]
  rw[div_add_div_same]
  rw[mul_comm, add_mul]
  rw[add_assoc]
  norm_num
  rw[mul_comm]
  linarith
