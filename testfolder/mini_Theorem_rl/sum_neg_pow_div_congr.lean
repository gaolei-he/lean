import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Lean4Repl

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem sum_neg_pow_div_congr : ∑ x in Ico 1 (n + 2), (-1 : ℝ) ^ (x+1) * (1 / x) * (Nat.choose (n + 1) x) = ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ ( 1 + x + 1 ) * (1 / (1 + x)) * (Nat.choose (n + 1) (1 + x)) := by lean_repl sorry
    rw[sum_Ico_eq_sum_range]
    simp
