import Theorem.example_separate.sum_mul_choose_eq_mul_two_pow_sub

open Nat

open Finset

open BigOperators


theorem sum_succ_choose(hn :0 < n) :  ∑ k in range (n+1), (k+1) * choose n k = 2 ^ (n - 1) * (n + 2) := by
  have sum_mul_add_distrib : ∑ k in range (n+1), (k+1) * choose n k = ∑ k in range (n+1), (k * choose n k + 1 * choose n k) := by
    refine' sum_congr rfl fun y _ => _
    rw[add_mul]
  rw[sum_mul_add_distrib]
  rw[sum_add_distrib]
  rw[sum_mul_choose_eq_mul_two_pow_sub hn]
  simp
  rw [sum_range_choose]
  have pow_eq_sub_one_mul :  2 ^ n = 2 ^ (n - 1) * 2  := by
    have n1 : 1 ≤ n := by linarith
    have h2n:  2 ^ (n - 1 + 1)=  2 ^ n := by
      rw[Nat.sub_add_cancel n1]
    rw[← h2n]
    rw[Nat.pow_succ]
  rw[pow_eq_sub_one_mul]
  rw[mul_comm, mul_add]
