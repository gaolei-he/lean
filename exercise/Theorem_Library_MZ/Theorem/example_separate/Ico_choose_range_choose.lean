import Theorem.example_separate.sum_choose_eq_Ico

open Nat

open Finset

open BigOperators

theorem Ico_choose_range_choose:  ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k)  = (∑ k in range (n + 1), choose (2 * n) k) - choose (2 * n) n := by  -- bn = an - choose (2 * n) n
  have sum_choose_sub_eq_add_sub : ∑ k in range (n + 1), choose (2 * n) k - (choose (2 * n) n) = (∑ k in range n, choose (2 * n) k) + (choose (2 * n) n) - (choose (2 * n) n) := by rw[Finset.sum_range_succ] -- an - (choose (2 * n) n) = (∑ k in range n, choose (2 * n) k)
  rw[← sum_choose_eq_Ico]
  simp at sum_choose_sub_eq_add_sub
  rw[sum_choose_sub_eq_add_sub]
  linarith


theorem Ico_choose_range_choose_from_0_to_0(n : ℕ)(gol:  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =
    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n) :
   ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =
    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n := by
  have sum_choose_sub_eq_add_sub : ∑ k in range (n + 1), choose (2 * n) k - (choose (2 * n) n) = (∑ k in range n, choose (2 * n) k) + (choose (2 * n) n) - (choose (2 * n) n) := by rw[Finset.sum_range_succ]
  apply gol

theorem Ico_choose_range_choose_from_4_to_4(n : ℕ)(sum_choose_sub_eq_add_sub :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n =    ∑ k in range n, Nat.choose (2 * n) k + Nat.choose (2 * n) n - Nat.choose (2 * n) n) :
   n ≤ 2 * n := by
  linarith

