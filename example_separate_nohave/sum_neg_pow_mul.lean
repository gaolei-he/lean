import Theorem.example_separate.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators

theorem sum_neg_pow_mul(hn : 1 < n): ∑ k in range (n+1), (-1 : ℤ)^k * k * (choose n k)  = 0 := by
  have zero_lt_n : 0 < n := by linarith
  have n_sub_one : n - 1 ≠ 0 := by exact Nat.sub_ne_zero_of_lt hn
  have hk : ∑ k in range (n+1), (-1 : ℤ)^k * k * (choose n k)  = (-1 : ℤ)^0 * 0 * (choose n 0) + ∑ k in Ico 1 (n+1), (-1 : ℤ)^k * k * (choose n k) := by
    rw[range_eq_Ico]
    have n_succ: 0 < n + 1 := by linarith
    rw[sum_eq_sum_Ico_succ_bot n_succ]
    simp
  rw[hk]
  simp
  have neg_pow_mul_choose_mul_eq_mul_sub:  ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * k * (choose n k) = ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * n * (choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hyn : y ≤ n := by
      have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
      linarith
    rw[mul_assoc, mul_assoc]
    congr 1
    rw[← cast_mul,← cast_mul]
    rw[choose_mul_eq_mul_sub' hyn hy1]
  rw[neg_pow_mul_choose_mul_eq_mul_sub]
  have neg_pow_cancel : ∑ k in Ico 1 (n + 1), (-1 : ℤ) ^ k * n * (choose (n-1) (k-1)) =  ∑ k in Ico 1 (n + 1), (-1) ^ (k - 1) * (-1 : ℤ)* n * (choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hnegy : (-1 : ℤ ) ^ y = (-1) ^ (y - 1 + 1)  := by
      rw[Nat.sub_add_cancel hy1]
    congr 2
  have neg_pow_mul_mul_mul : ∑ k in Ico 1 (n + 1), (-1 : ℤ) ^ (k - 1) * (-1)* n * (choose (n-1) (k-1))  = ∑ k in Ico 1 (n + 1), (-1 : ℤ)*  ((-1) ^ (k - 1) * n * (choose (n-1) (k-1)) ) := by
    refine' sum_congr rfl fun y hy => _
    rw[mul_comm ((-1 : ℤ) ^ (y - 1)) (-1)]
    rw[mul_assoc,mul_assoc,mul_assoc]
  rw[neg_pow_cancel,neg_pow_mul_mul_mul]
  rw[← mul_sum]
  simp
  rw[sum_Ico_eq_sum_range]
  simp
  have sum_neg_comm : ∑ x in range n, (-1 : ℤ) ^ x * n * ↑(Nat.choose (n - 1) x) =  ∑ x in range n, n * (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x):= by
    refine' sum_congr rfl fun y hy => _
    congr 1
    rw[mul_comm]
  have sum_neg_assoc: ∑ x in range n, n * (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) =  ∑ x in range n, n * ((-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x)) := by
    refine' sum_congr rfl fun y hy => _
    rw[mul_assoc]
  rw[sum_neg_comm, sum_neg_assoc, ← mul_sum]
  simp
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  rw[sum_neg_cancel]
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  simp
