import Theorem.example_separate.add_div_two
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem div_mul_Ico_eq_zero :
 1 / (2 * m + 1) * ∑ l in Ico 0 (2 * m), (l+1) * (-1 : ℝ ) ^ (l+1) / choose (2 * m) l = 0 := by sorry


theorem div_mul_Ico_eq_zero_from_0_to_0(m : ℕ) :
   1 / (2 * ↑m + 1) * ∑ l in Ico 0 (2 * m), (↑l + 1) * (-1 : ℝ) ^ (l + 1) / ↑(Nat.choose (2 * m) l) = 0 := by
  sorry

