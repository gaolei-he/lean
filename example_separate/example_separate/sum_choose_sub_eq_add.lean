import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem sum_choose_sub_eq_add : ∑ k in range (n + 1), choose (2 * n) k - (choose (2 * n) n) = (∑ k in range n, choose (2 * n) k) := by
  rw[Finset.sum_range_succ]
  simp
