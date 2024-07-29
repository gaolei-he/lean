import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Lean4Repl

set_option maxHeartbeats 999999999999999999999999

theorem inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by lean_repl sorry
  rw[div_eq_mul_one_div]
  rw[mul_comm, mul_assoc]
