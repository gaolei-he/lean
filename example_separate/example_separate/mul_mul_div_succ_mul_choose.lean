import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


theorem mul_mul_div_succ_mul_choose{n k: ℕ} : (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) : ℝ) * ↑(Nat.choose n k)
  = (↑n + 1) * (↑k + 1) * ((1 / (↑k + 1)) * ↑(Nat.choose n k)) := by
  exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑k + 1)) ↑(Nat.choose n k)
