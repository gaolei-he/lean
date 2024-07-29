import Theorem.example_separate.add_div_two
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem div_mul_Ico_eq_zero : 1 / (2 * m + 1) * ∑ l in Ico 0 (2 * m), (l+1) * (-1 : ℝ ) ^ (l+1) / choose (2 * m) l = 0 := by sorry
