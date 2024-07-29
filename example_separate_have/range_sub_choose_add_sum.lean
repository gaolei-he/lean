import Theorem.example_separate.range_sub_choose
import Theorem.example_separate.two_pow_eq_range_add_ico


open Nat

open Finset

open BigOperators

theorem range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by
  rw[← range_sub_choose, Nat.add_comm]
  rw[←two_pow_eq_range_add_ico]
