import Theorem.example_separate.add_div_two
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators


theorem Ico_neg_eq_succ : ∑ k in Ico 1 (2 * n), (-1 : ℝ) ^ (k - 1) / choose (2 * n) k = 1 / (n + 1) := by sorry
