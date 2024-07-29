import Mathlib.Data.Real.Basic


theorem two_m_div_add{m : ℕ}(hm : 0 < m) : 2 * (m + 1) / (m + 1)  + (-1 : ℝ) / (m + 1) = 2 + (-1 : ℝ) / (m + 1) := by
  congr 1
  rw[mul_div_assoc]
  simp
  rw[div_self]
  linarith
