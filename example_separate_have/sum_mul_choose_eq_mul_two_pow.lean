import Theorem.example_separate.sum_range_succ_eq_sum_range
import Theorem.example_separate.sum_range_choose_halfway_of_lt

open Nat

open Finset

open BigOperators


theorem sum_mul_choose_eq_mul_two_pow (h : 0 < n) : ∑ k in range (n+1), (k * choose (2 * n) k) = n * 2 ^ (2 * n - 1) := by
  rw[sum_range_succ_eq_sum_range]
  rw[sum_range_choose_halfway_of_lt n h] --(2 * n) * 2 ^ (2 * n - 2)
  rw[mul_comm 2 n, mul_assoc]
  congr 1
  rw[mul_comm]
  -- have h1 : 2 ^ (n * 2 - 1) = 2 ^ (n * 2 - 2 + 1) := by
  rw[← Nat.pow_succ]
  congr 1
  rw[Nat.succ_eq_add_one]
  have h1 : 1 ≤ n * 2 := by linarith
  have h2 : 2 ≤ n * 2 := by linarith
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  simp at h21
  rw[h21]
