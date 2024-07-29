import Theorem.example_separate.mul_choose_eq_mul_choose
import Theorem.example_separate.sum_mul_congr
import Theorem.example_separate.mul_choose_two_pow

open Nat

open Finset

open BigOperators


theorem sum_mul_choose_eq_mul_two_pow_sub(hn :0 < n) : ∑ k in range (n+1), k * choose n k = n * 2 ^(n-1) := by
  rw[mul_choose_eq_mul_choose hn]
  rw[sum_mul_congr]
  rw[mul_choose_two_pow hn]
