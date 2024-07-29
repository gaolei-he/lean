import Theorem.example_separate.choose_le_sum
import Theorem.example_separate.range_sub_choose_add_sum

open Nat

open Finset

open BigOperators


theorem sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   -- an + an = 2 ^ ( 2 * n ) + choose (2 * n) n
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by
      rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
      simp
      rw [Nat.sub_add_cancel choose_le_sum]
  rw[←sum_sub_sum_add,sum_add_eq_add]
