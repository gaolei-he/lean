import AdaLean.sum_choose_eq_Ico

open Nat

open Finset

open BigOperators

theorem sum_choose_sub_eq_add_sub : ∑ k in range (n + 1), choose (2 * n) k - (choose (2 * n) n) = (∑ k in range n, choose (2 * n) k) := by
  rw[Finset.sum_range_succ]
  simp
