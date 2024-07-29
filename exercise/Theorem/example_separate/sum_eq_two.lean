import Mathlib.Data.Nat.Choose.Sum


open Nat

open Finset

open BigOperators

theorem sum_eq_two (n : Nat):
  2 ^ ( 2 * n ) = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by
   have h : n + 1 ≤ 2 * n + 1 := by linarith
   rw [Finset.sum_range_add_sum_Ico _ (h)]
   rw [← sum_range_choose]


theorem sum_eq_two_from_0_to_0(n : ℕ)(gol:  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k) :
   2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k := by
  have h : n + 1 ≤ 2 * n + 1 := by linarith
  apply gol

theorem sum_eq_two_from_0_to_1(n : ℕ)(gol:  2 ^ (2 * n) = ∑ k in range (2 * n + 1), Nat.choose (2 * n) k) :
   2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k := by
  have h : n + 1 ≤ 2 * n + 1 := by linarith
  rw [Finset.sum_range_add_sum_Ico _ (h)]
  apply gol

theorem sum_eq_two_from_0_to_2(n : ℕ) :
   2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k := by
  have h : n + 1 ≤ 2 * n + 1 := by linarith
  rw [Finset.sum_range_add_sum_Ico _ (h)]
  rw [← sum_range_choose]

theorem sum_eq_two_from_1_to_1(n : ℕ)(h : n + 1 ≤ 2 * n + 1)(gol:  2 ^ (2 * n) = ∑ k in range (2 * n + 1), Nat.choose (2 * n) k) :
   2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k := by
  rw [Finset.sum_range_add_sum_Ico _ (h)]
  apply gol

theorem sum_eq_two_from_1_to_2(n : ℕ)(h : n + 1 ≤ 2 * n + 1) :
   2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k := by
  rw [Finset.sum_range_add_sum_Ico _ (h)]
  rw [← sum_range_choose]

theorem sum_eq_two_from_2_to_2(n : ℕ)(h : n + 1 ≤ 2 * n + 1) :
   2 ^ (2 * n) = ∑ k in range (2 * n + 1), Nat.choose (2 * n) k := by
  rw [← sum_range_choose]

