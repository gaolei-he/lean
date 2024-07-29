import Mathlib.Data.Nat.Choose.Sum


open Nat

open Finset

open BigOperators

theorem sum_eq_two (n : Nat):
  2 ^ ( 2 * n ) = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by
   have h : n + 1 ≤ 2 * n + 1 := by linarith
   rw [Finset.sum_range_add_sum_Ico _ (h)]
   rw [← sum_range_choose]
