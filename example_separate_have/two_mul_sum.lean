import Theorem.example_separate.sum_add_eq_two_pow

open Nat

open Finset

open BigOperators


theorem two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  -- 2 * an = 2 ^ ( 2 * n ) + choose (2 * n) n
  rw[← sum_add_eq_two_pow, two_mul]
