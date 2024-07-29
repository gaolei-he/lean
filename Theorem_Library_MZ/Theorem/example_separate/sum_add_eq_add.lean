import Theorem.example_separate.range_sub_choose_add_sum

open Nat

open Finset

open BigOperators


theorem sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]


theorem sum_add_eq_add_from_0_to_0(n : ℕ) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +
      Nat.choose (2 * n) n =
    2 ^ (2 * n) + Nat.choose (2 * n) n := by
  rw[range_sub_choose_add_sum]

