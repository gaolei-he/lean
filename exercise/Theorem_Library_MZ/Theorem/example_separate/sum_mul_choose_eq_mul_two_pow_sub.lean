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


theorem sum_mul_choose_eq_mul_two_pow_sub_from_0_to_0(n : ℕ)(hn : 0 < n)(gol:  ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) = n * 2 ^ (n - 1)) :
   ∑ k in range (n + 1), k * Nat.choose n k = n * 2 ^ (n - 1) := by
  rw[mul_choose_eq_mul_choose hn]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_sub_from_2_to_2(n : ℕ)(hn : 0 < n) :
   n * ∑ l in range n, Nat.choose (n - 1) l = n * 2 ^ (n - 1) := by
  rw[mul_choose_two_pow hn]

