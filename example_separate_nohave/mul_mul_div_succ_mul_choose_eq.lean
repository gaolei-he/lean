import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat


theorem mul_mul_div_succ_mul_choose_eq{n k: ℕ} :  (n+1) * (k+1) * ((1/(k+1)) : ℝ) * choose n k = (n+1) * (k+1) * (1/(n+1)) * choose (n+1) (k+1) := by
    have h1 : (k : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero k
    rw [mul_comm, mul_assoc]
    rw [mul_one_div_cancel h1]
    have h2 : (n + 1) * (k + 1) * ((1 / (n+1)) : ℝ) * (Nat.choose (n + 1) (k + 1))
      = (k + 1) * ((n + 1) * (1 / (n+1)) * (Nat.choose (n + 1) (k + 1))) := by
      rw [←mul_assoc]
      congr 1
      rw [←mul_assoc]
      congr 1
      rw [mul_comm]
    rw [h2]
    rw [←mul_assoc]
    have h3 : (n : ℝ)+1 ≠ 0 := by exact cast_add_one_ne_zero n
    rw [mul_one_div_cancel h3]
    simp
    rw [mul_comm, ←cast_one, ←cast_add, ←cast_add, ←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq]
    simp [mul_comm]
