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


theorem sum_mul_choose_eq_mul_two_pow_from_0_to_0(n : ℕ)(h : 0 < n)(gol:  2 * n * ∑ k in range n, Nat.choose (2 * n - 1) k = n * 2 ^ (2 * n - 1)) :
   ∑ k in range (n + 1), k * Nat.choose (2 * n) k = n * 2 ^ (2 * n - 1) := by
  rw[sum_range_succ_eq_sum_range]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_0_to_1(n : ℕ)(h : 0 < n)(gol:  2 * n * 2 ^ (2 * n - 2) = n * 2 ^ (2 * n - 1)) :
   ∑ k in range (n + 1), k * Nat.choose (2 * n) k = n * 2 ^ (2 * n - 1) := by
  rw[sum_range_succ_eq_sum_range]
  rw[sum_range_choose_halfway_of_lt n h]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_0_to_2(n : ℕ)(h : 0 < n)(gol:  n * (2 * 2 ^ (n * 2 - 2)) = n * 2 ^ (n * 2 - 1)) :
   ∑ k in range (n + 1), k * Nat.choose (2 * n) k = n * 2 ^ (2 * n - 1) := by
  rw[sum_range_succ_eq_sum_range]
  rw[sum_range_choose_halfway_of_lt n h]
  rw[mul_comm 2 n, mul_assoc]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_1_to_1(n : ℕ)(h : 0 < n)(gol:  2 * n * 2 ^ (2 * n - 2) = n * 2 ^ (2 * n - 1)) :
   2 * n * ∑ k in range n, Nat.choose (2 * n - 1) k = n * 2 ^ (2 * n - 1) := by
  rw[sum_range_choose_halfway_of_lt n h]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_1_to_2(n : ℕ)(h : 0 < n)(gol:  n * (2 * 2 ^ (n * 2 - 2)) = n * 2 ^ (n * 2 - 1)) :
   2 * n * ∑ k in range n, Nat.choose (2 * n - 1) k = n * 2 ^ (2 * n - 1) := by
  rw[sum_range_choose_halfway_of_lt n h]
  rw[mul_comm 2 n, mul_assoc]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_2_to_2(n : ℕ)(h : 0 < n)(gol:  n * (2 * 2 ^ (n * 2 - 2)) = n * 2 ^ (n * 2 - 1)) :
   2 * n * 2 ^ (2 * n - 2) = n * 2 ^ (2 * n - 1) := by
  rw[mul_comm 2 n, mul_assoc]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_4_to_4(n : ℕ)(h : 0 < n)(gol:  2 ^ (n * 2 - 2) * 2 = 2 ^ (n * 2 - 1)) :
   2 * 2 ^ (n * 2 - 2) = 2 ^ (n * 2 - 1) := by
  rw[mul_comm]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_4_to_5(n : ℕ)(h : 0 < n)(gol:  2 ^ succ (n * 2 - 2) = 2 ^ (n * 2 - 1)) :
   2 * 2 ^ (n * 2 - 2) = 2 ^ (n * 2 - 1) := by
  rw[mul_comm]
  rw[← Nat.pow_succ]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_5_to_5(n : ℕ)(h : 0 < n)(gol:  2 ^ succ (n * 2 - 2) = 2 ^ (n * 2 - 1)) :
   2 ^ (n * 2 - 2) * 2 = 2 ^ (n * 2 - 1) := by
  rw[← Nat.pow_succ]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_7_to_7(n : ℕ)(h : 0 < n)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   succ (n * 2 - 2) = n * 2 - 1 := by
  rw[Nat.succ_eq_add_one]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_7_to_8(n : ℕ)(h : 0 < n)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   succ (n * 2 - 2) = n * 2 - 1 := by
  rw[Nat.succ_eq_add_one]
  have h1 : 1 ≤ n * 2 := by linarith
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_7_to_9(n : ℕ)(h : 0 < n)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   succ (n * 2 - 2) = n * 2 - 1 := by
  rw[Nat.succ_eq_add_one]
  have h1 : 1 ≤ n * 2 := by linarith
  have h2 : 2 ≤ n * 2 := by linarith
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_7_to_10(n : ℕ)(h : 0 < n)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   succ (n * 2 - 2) = n * 2 - 1 := by
  rw[Nat.succ_eq_add_one]
  have h1 : 1 ≤ n * 2 := by linarith
  have h2 : 2 ≤ n * 2 := by linarith
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_7_to_11(n : ℕ)(h : 0 < n)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   succ (n * 2 - 2) = n * 2 - 1 := by
  rw[Nat.succ_eq_add_one]
  have h1 : 1 ≤ n * 2 := by linarith
  have h2 : 2 ≤ n * 2 := by linarith
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  simp at h21
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_7_to_12(n : ℕ)(h : 0 < n) :
   succ (n * 2 - 2) = n * 2 - 1 := by
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

theorem sum_mul_choose_eq_mul_two_pow_from_8_to_8(n : ℕ)(h : 0 < n)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h1 : 1 ≤ n * 2 := by linarith
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_8_to_9(n : ℕ)(h : 0 < n)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h1 : 1 ≤ n * 2 := by linarith
  have h2 : 2 ≤ n * 2 := by linarith
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_8_to_10(n : ℕ)(h : 0 < n)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h1 : 1 ≤ n * 2 := by linarith
  have h2 : 2 ≤ n * 2 := by linarith
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_8_to_11(n : ℕ)(h : 0 < n)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h1 : 1 ≤ n * 2 := by linarith
  have h2 : 2 ≤ n * 2 := by linarith
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  simp at h21
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_8_to_12(n : ℕ)(h : 0 < n) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h1 : 1 ≤ n * 2 := by linarith
  have h2 : 2 ≤ n * 2 := by linarith
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  simp at h21
  rw[h21]

theorem sum_mul_choose_eq_mul_two_pow_from_9_to_9(n : ℕ)(h : 0 < n)(h1 : 1 ≤ n * 2)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h2 : 2 ≤ n * 2 := by linarith
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_9_to_10(n : ℕ)(h : 0 < n)(h1 : 1 ≤ n * 2)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h2 : 2 ≤ n * 2 := by linarith
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_9_to_11(n : ℕ)(h : 0 < n)(h1 : 1 ≤ n * 2)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h2 : 2 ≤ n * 2 := by linarith
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  simp at h21
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_9_to_12(n : ℕ)(h : 0 < n)(h1 : 1 ≤ n * 2) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h2 : 2 ≤ n * 2 := by linarith
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  simp at h21
  rw[h21]

theorem sum_mul_choose_eq_mul_two_pow_from_10_to_10(n : ℕ)(h : 0 < n)(h1 : 1 ≤ n * 2)(h2 : 2 ≤ n * 2)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_10_to_11(n : ℕ)(h : 0 < n)(h1 : 1 ≤ n * 2)(h2 : 2 ≤ n * 2)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  simp at h21
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_10_to_12(n : ℕ)(h : 0 < n)(h1 : 1 ≤ n * 2)(h2 : 2 ≤ n * 2) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  have h21: n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1 := by
    rw[Nat.sub_add_cancel h1]
    rw[add_assoc]
    norm_num
    rw[Nat.sub_add_cancel h2]
  simp at h21
  rw[h21]

theorem sum_mul_choose_eq_mul_two_pow_from_11_to_11(n : ℕ)(h : 0 < n)(h1 : 1 ≤ n * 2)(h2 : 2 ≤ n * 2)(h21 : n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1)(gol:  n * 2 - 2 + 1 = n * 2 - 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  simp at h21
  apply gol

theorem sum_mul_choose_eq_mul_two_pow_from_11_to_12(n : ℕ)(h : 0 < n)(h1 : 1 ≤ n * 2)(h2 : 2 ≤ n * 2)(h21 : n * 2 - 1 + 1 = n * 2 - 2 + 1 + 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  simp at h21
  rw[h21]

theorem sum_mul_choose_eq_mul_two_pow_from_12_to_12(n : ℕ)(h : 0 < n)(h1 : 1 ≤ n * 2)(h2 : 2 ≤ n * 2)(h21 : n * 2 - 1 = n * 2 - 2 + 1) :
   n * 2 - 2 + 1 = n * 2 - 1 := by
  rw[h21]

