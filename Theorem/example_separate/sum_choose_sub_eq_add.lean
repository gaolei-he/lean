import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem sum_choose_sub_eq_add : ∑ k in range (n + 1), choose (2 * n) k - (choose (2 * n) n) = (∑ k in range n, choose (2 * n) k) := by
  rw[Finset.sum_range_succ]
  simp


theorem sum_choose_sub_eq_add_from_0_to_0(n : ℕ)(gol:  ∑ x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n - Nat.choose (2 * n) n =
    ∑ k in range n, Nat.choose (2 * n) k) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n = ∑ k in range n, Nat.choose (2 * n) k := by
  rw[Finset.sum_range_succ]
  apply gol

theorem sum_choose_sub_eq_add_from_0_to_1(n : ℕ) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n = ∑ k in range n, Nat.choose (2 * n) k := by
  rw[Finset.sum_range_succ]
  simp

theorem sum_choose_sub_eq_add_from_1_to_1(n : ℕ) :
   ∑ x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n - Nat.choose (2 * n) n =
    ∑ k in range n, Nat.choose (2 * n) k := by
  simp

