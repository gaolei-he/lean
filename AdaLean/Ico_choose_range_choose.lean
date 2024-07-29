import AdaLean.sum_choose_eq_Ico
import AdaLean.sum_choose_sub_eq_add_sub

open Nat

open Finset

open BigOperators

theorem Ico_choose_range_choose:  ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k)  = (∑ k in range (n + 1), choose (2 * n) k) - choose (2 * n) n := by
  rw[← sum_choose_eq_Ico]
  rw[sum_choose_sub_eq_add_sub]
  linarith
