import Mathlib.Data.Real.Basic
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999
theorem two_mul_div_add{m : ℕ}: 2 * (m + 1) / (m + 1)  + (-1 : ℝ) / (m + 1) = 2 + (-1 : ℝ) / (m + 1) := by lean_repl sorry
    congr 1
    rw[mul_div_assoc]
    simp
    rw[div_self]
    linarith
