import AdaLean.choose_le_sum
import AdaLean.range_sub_choose_add_sum
import AdaLean.sum_sub_sum_add

open Nat

open Finset

open BigOperators


theorem sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
