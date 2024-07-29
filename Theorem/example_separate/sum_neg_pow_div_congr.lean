import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Finset

open BigOperators

theorem sum_neg_pow_div_congr : ∑ x in Ico 1 (n + 2), (-1 : ℝ) ^ (x+1) * (1 / x) * (Nat.choose (n + 1) x) = ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ ( 1 + x + 1 ) * (1 / (1 + x)) * (Nat.choose (n + 1) (1 + x)) := by
    rw[sum_Ico_eq_sum_range]
    simp


theorem sum_neg_pow_div_congr_from_0_to_0(n : ℕ)(gol:  ∑ k in range (n + 2 - 1), (-1 : ℝ) ^ (1 + k + 1) * (1 / ↑(1 + k)) * ↑(Nat.choose (n + 1) (1 + k)) =
    ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ (1 + x + 1) * (1 / (1 + ↑x)) * ↑(Nat.choose (n + 1) (1 + x))) :
   ∑ x in Ico 1 (n + 2), (-1 : ℝ) ^ (x + 1) * (1 / ↑x) * ↑(Nat.choose (n + 1) x) =
    ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ (1 + x + 1) * (1 / (1 + ↑x)) * ↑(Nat.choose (n + 1) (1 + x)) := by
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem sum_neg_pow_div_congr_from_0_to_1(n : ℕ) :
   ∑ x in Ico 1 (n + 2), (-1 : ℝ) ^ (x + 1) * (1 / ↑x) * ↑(Nat.choose (n + 1) x) =
    ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ (1 + x + 1) * (1 / (1 + ↑x)) * ↑(Nat.choose (n + 1) (1 + x)) := by
  rw[sum_Ico_eq_sum_range]
  simp

theorem sum_neg_pow_div_congr_from_1_to_1(n : ℕ) :
   ∑ k in range (n + 2 - 1), (-1 : ℝ) ^ (1 + k + 1) * (1 / ↑(1 + k)) * ↑(Nat.choose (n + 1) (1 + k)) =
    ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ (1 + x + 1) * (1 / (1 + ↑x)) * ↑(Nat.choose (n + 1) (1 + x)) := by
  simp

