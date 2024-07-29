import Theorem.example_separate.two_mul_sum

open Nat

open Finset

open BigOperators

theorem sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]  -- an = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2
