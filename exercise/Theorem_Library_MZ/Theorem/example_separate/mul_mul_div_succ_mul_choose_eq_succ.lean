import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic



theorem mul_mul_div_succ_mul_choose_eq_succ{n k: ℕ} : (↑n + 1) * (↑k + 1) * ((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))
  = (↑n + 1) * (↑k + 1) * (((1 / (↑n + 1)) : ℝ ) * ↑(Nat.choose (n + 1) (k + 1))) := by
  exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))


theorem mul_mul_div_succ_mul_choose_eq_succ_from_0_to_0(n k : ℕ) :
   (↑n + 1) * (↑k + 1) * (1 / (↑n + 1)) * ↑(Nat.choose (n + 1) (k + 1)) =
    (↑n + 1) * (↑k + 1) * (1 / (↑n + 1) * ↑(Nat.choose (n + 1) (k + 1))) := by
  exact mul_assoc ((↑n + 1) * (↑k + 1) : ℝ) (1 / (↑n + 1)) ↑(Nat.choose (n + 1) (k + 1))

