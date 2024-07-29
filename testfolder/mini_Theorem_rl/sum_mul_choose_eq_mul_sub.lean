import Theorem.example_separate.bot_sum_mul_congr
import Theorem.example_separate.mul_sum_choose
import Theorem.example_separate.mul_sum_choose_sub_choose
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem sum_mul_choose_eq_mul_sub : ∑ k in range (n+1), ((k * choose (2 * n + 1) k):ℝ) = (2 * n + 1) * (2 ^ ( 2 * n - 1 ) - ((choose (2*n) n/ 2:ℝ))) := by lean_repl sorry
  rw[bot_sum_mul_congr, mul_sum_choose, mul_sum_choose_sub_choose]
