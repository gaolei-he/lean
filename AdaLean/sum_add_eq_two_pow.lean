import AdaLean.choose_le_sum
import AdaLean.range_sub_choose_add_sum
import AdaLean.sum_sub_sum_add
import AdaLean.sum_add_eq_add

open Nat

open Finset

open BigOperators


theorem sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by
  rw[←sum_sub_sum_add]
  rw[sum_add_eq_add]
