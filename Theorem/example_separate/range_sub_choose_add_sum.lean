import Theorem.example_separate.range_sub_choose
import Theorem.example_separate.two_pow_eq_range_add_ico


open Nat

open Finset

open BigOperators

theorem range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by
  rw[← range_sub_choose, Nat.add_comm]
  rw[←two_pow_eq_range_add_ico]


theorem range_sub_choose_add_sum_from_0_to_0(n : ℕ)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n)) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =
    2 ^ (2 * n) := by
  rw[← range_sub_choose, Nat.add_comm]
  apply gol

theorem range_sub_choose_add_sum_from_0_to_1(n : ℕ) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =
    2 ^ (2 * n) := by
  rw[← range_sub_choose, Nat.add_comm]
  rw[←two_pow_eq_range_add_ico]

theorem range_sub_choose_add_sum_from_1_to_1(n : ℕ) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n) := by
  rw[←two_pow_eq_range_add_ico]

