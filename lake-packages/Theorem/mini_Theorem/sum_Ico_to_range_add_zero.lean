import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators


theorem sum_Ico_to_range_add_zero {n : ℕ} : ∑ k in Ico 1 (n + 1), k * choose (2*n) k = ∑ k in range (n+1), k * choose (2*n) k := by
  have h_gt_zero : 0 < n + 1 := by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h_gt_zero]
  simp
