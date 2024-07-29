import Mathlib.Data.Real.Basic


theorem two_mul_div_add{m : ℕ }: 2 * (m + 1) / (m + 1)  + (-1 : ℝ) / (m + 1) = 2 + (-1 : ℝ) / (m + 1) := by
    congr 1
    rw[mul_div_assoc]
    simp
    rw[div_self]
    linarith
