import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Finset

open BigOperators

theorem sum_neg_pow_div_congr : ∑ x in Ico 1 (n + 2), (-1 : ℝ) ^ (x+1) * (1 / x) * (Nat.choose (n + 1) x) = ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ ( 1 + x + 1 ) * (1 / (1 + x)) * (Nat.choose (n + 1) (1 + x)) := by
    rw[sum_Ico_eq_sum_range]
    simp
