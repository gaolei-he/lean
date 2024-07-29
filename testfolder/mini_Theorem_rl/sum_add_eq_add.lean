import Theorem.example_separate.range_sub_choose_add_sum
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by lean_repl sorry
  rw[range_sub_choose_add_sum]
