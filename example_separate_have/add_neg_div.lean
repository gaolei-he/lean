import Mathlib.Data.Real.Basic


theorem add_neg_div {m : ℕ }(hm : 0 < m): 2 + (-1 : ℝ) / (m + 1) = (2 * m + 1) / (m + 1) := by   -- 第四个等式
  have two_m_div_add : 2 * (m + 1) / (m + 1)  + (-1 : ℝ) / (m + 1) = 2 + (-1 : ℝ) / (m + 1) := by
    congr 1
    rw[mul_div_assoc]
    simp
    have m_r : 0 < (m : ℝ) := by
      simp
      exact hm
    have hm_z : (m : ℝ) + 1 ≠ 0  := by
      linarith
    rw[div_self hm_z]
  rw[← two_m_div_add]
  rw[div_add_div_same]  -- 除法分配律
  rw[mul_comm, add_mul]
  rw[add_assoc]
  norm_num
  rw[mul_comm]
