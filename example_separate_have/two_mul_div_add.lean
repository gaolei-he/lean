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
