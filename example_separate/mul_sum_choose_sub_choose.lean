import Theorem.example_separate.choose_eq_pow_add
import Lean4Repl
open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem mul_sum_choose_sub_choose : (2 * n + 1) * ((∑ k in range (n+1), ((choose (2*n) k):ℝ)) - ((choose (2*n) n:ℝ))) = (2 * n + 1) * (2 ^ ( 2 * n - 1 ) - ((choose (2*n) n/ 2:ℝ))) := by lean_repl sorry
  rw[choose_eq_pow_add]
  congr 1
  rw[← add_sub]
  rw[div_two_sub_self]
  rw[← sub_eq_add_neg]
