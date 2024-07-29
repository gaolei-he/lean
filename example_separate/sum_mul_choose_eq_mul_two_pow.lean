import Theorem.example_separate.sum_range_succ_eq_sum_range
import Theorem.example_separate.sum_range_choose_halfway_of_lt
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem sum_mul_choose_eq_mul_two_pow (h : 0 < n) : ∑ k in range (n+1), (k * choose (2 * n) k) = n * 2 ^ (2 * n - 1) := by lean_repl sorry
  rw[sum_range_succ_eq_sum_range]
  rw[sum_range_choose_halfway_of_lt n h] --(2 * n) * 2 ^ (2 * n - 2)
  rw[mul_comm 2 n, mul_assoc]
  congr 1
  rw[mul_comm]
  rw[← Nat.pow_succ]
  congr 1
  rw[Nat.succ_eq_add_one]
  rw[← Nat.sub_add_comm]
  simp
  linarith
