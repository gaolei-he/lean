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


theorem sum_neg_pow_mul_from_0_to_0(n : ℕ)(hn : 1 < n)(gol:  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  have zero_lt_n : 0 < n := by linarith
  apply gol

theorem sum_neg_pow_mul_from_0_to_1(n : ℕ)(hn : 1 < n)(gol:  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  have zero_lt_n : 0 < n := by linarith
  have n_sub_one : n - 1 ≠ 0 := by exact Nat.sub_ne_zero_of_lt hn
  apply gol

theorem sum_neg_pow_mul_from_1_to_1(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(gol:  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  have n_sub_one : n - 1 ≠ 0 := by exact Nat.sub_ne_zero_of_lt hn
  apply gol

theorem sum_neg_pow_mul_from_3_to_3(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(gol:  (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  rw[hk]
  apply gol

theorem sum_neg_pow_mul_from_3_to_4(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(gol:  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  rw[hk]
  simp
  apply gol

theorem sum_neg_pow_mul_from_4_to_4(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(gol:  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  simp
  apply gol

theorem sum_neg_pow_mul_from_6_to_6(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(gol:  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  rw[neg_pow_mul_choose_mul_eq_mul_sub]
  apply gol

theorem sum_neg_pow_mul_from_9_to_9(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) = 0 := by
  rw[neg_pow_cancel,neg_pow_mul_mul_mul]
  apply gol

theorem sum_neg_pow_mul_from_9_to_10(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  -1 * ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ (x - 1) * ↑n * ↑(Nat.choose (n - 1) (x - 1)) = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) = 0 := by
  rw[neg_pow_cancel,neg_pow_mul_mul_mul]
  rw[← mul_sum]
  apply gol

theorem sum_neg_pow_mul_from_9_to_11(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ (x - 1) * ↑n * ↑(Nat.choose (n - 1) (x - 1)) = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) = 0 := by
  rw[neg_pow_cancel,neg_pow_mul_mul_mul]
  rw[← mul_sum]
  simp
  apply gol

theorem sum_neg_pow_mul_from_9_to_12(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k - 1) * ↑n * ↑(Nat.choose (n - 1) (1 + k - 1)) = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) = 0 := by
  rw[neg_pow_cancel,neg_pow_mul_mul_mul]
  rw[← mul_sum]
  simp
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem sum_neg_pow_mul_from_9_to_13(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) = 0 := by
  rw[neg_pow_cancel,neg_pow_mul_mul_mul]
  rw[← mul_sum]
  simp
  rw[sum_Ico_eq_sum_range]
  simp
  apply gol

theorem sum_neg_pow_mul_from_10_to_10(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  -1 * ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ (x - 1) * ↑n * ↑(Nat.choose (n - 1) (x - 1)) = 0) :
   ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw[← mul_sum]
  apply gol

theorem sum_neg_pow_mul_from_10_to_11(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ (x - 1) * ↑n * ↑(Nat.choose (n - 1) (x - 1)) = 0) :
   ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw[← mul_sum]
  simp
  apply gol

theorem sum_neg_pow_mul_from_10_to_12(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k - 1) * ↑n * ↑(Nat.choose (n - 1) (1 + k - 1)) = 0) :
   ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw[← mul_sum]
  simp
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem sum_neg_pow_mul_from_10_to_13(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw[← mul_sum]
  simp
  rw[sum_Ico_eq_sum_range]
  simp
  apply gol

theorem sum_neg_pow_mul_from_11_to_11(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ (x - 1) * ↑n * ↑(Nat.choose (n - 1) (x - 1)) = 0) :
   -1 * ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ (x - 1) * ↑n * ↑(Nat.choose (n - 1) (x - 1)) = 0 := by
  simp
  apply gol

theorem sum_neg_pow_mul_from_11_to_12(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k - 1) * ↑n * ↑(Nat.choose (n - 1) (1 + k - 1)) = 0) :
   -1 * ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ (x - 1) * ↑n * ↑(Nat.choose (n - 1) (x - 1)) = 0 := by
  simp
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem sum_neg_pow_mul_from_11_to_13(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = 0) :
   -1 * ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ (x - 1) * ↑n * ↑(Nat.choose (n - 1) (x - 1)) = 0 := by
  simp
  rw[sum_Ico_eq_sum_range]
  simp
  apply gol

theorem sum_neg_pow_mul_from_12_to_12(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k - 1) * ↑n * ↑(Nat.choose (n - 1) (1 + k - 1)) = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ (x - 1) * ↑n * ↑(Nat.choose (n - 1) (x - 1)) = 0 := by
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem sum_neg_pow_mul_from_12_to_13(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ (x - 1) * ↑n * ↑(Nat.choose (n - 1) (x - 1)) = 0 := by
  rw[sum_Ico_eq_sum_range]
  simp
  apply gol

theorem sum_neg_pow_mul_from_13_to_13(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k - 1) * ↑n * ↑(Nat.choose (n - 1) (1 + k - 1)) = 0 := by
  simp
  apply gol

theorem sum_neg_pow_mul_from_16_to_16(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  ↑n * ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = 0 := by
  rw[sum_neg_comm, sum_neg_assoc, ← mul_sum]
  apply gol

theorem sum_neg_pow_mul_from_16_to_17(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = 0 := by
  rw[sum_neg_comm, sum_neg_assoc, ← mul_sum]
  simp
  apply gol

theorem sum_neg_pow_mul_from_16_to_18(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = 0 := by
  rw[sum_neg_comm, sum_neg_assoc, ← mul_sum]
  simp
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  apply gol

theorem sum_neg_pow_mul_from_16_to_19(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  n = 0 ∨ ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = 0 := by
  rw[sum_neg_comm, sum_neg_assoc, ← mul_sum]
  simp
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  rw[sum_neg_cancel]
  apply gol

theorem sum_neg_pow_mul_from_16_to_20(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  n = 0 ∨ 0 = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = 0 := by
  rw[sum_neg_comm, sum_neg_assoc, ← mul_sum]
  simp
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  rw[sum_neg_cancel]
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  apply gol

theorem sum_neg_pow_mul_from_16_to_21(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))) :
   ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = 0 := by
  rw[sum_neg_comm, sum_neg_assoc, ← mul_sum]
  simp
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  rw[sum_neg_cancel]
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  simp

theorem sum_neg_pow_mul_from_17_to_17(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ↑n * ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  simp
  apply gol

theorem sum_neg_pow_mul_from_17_to_18(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ↑n * ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  simp
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  apply gol

theorem sum_neg_pow_mul_from_17_to_19(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  n = 0 ∨ ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ↑n * ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  simp
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  rw[sum_neg_cancel]
  apply gol

theorem sum_neg_pow_mul_from_17_to_20(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  n = 0 ∨ 0 = 0) :
   ↑n * ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  simp
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  rw[sum_neg_cancel]
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  apply gol

theorem sum_neg_pow_mul_from_17_to_21(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))) :
   ↑n * ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  simp
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  rw[sum_neg_cancel]
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  simp

theorem sum_neg_pow_mul_from_18_to_18(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  apply gol

theorem sum_neg_pow_mul_from_18_to_19(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  n = 0 ∨ ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  rw[sum_neg_cancel]
  apply gol

theorem sum_neg_pow_mul_from_18_to_20(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(gol:  n = 0 ∨ 0 = 0) :
   n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  rw[sum_neg_cancel]
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  apply gol

theorem sum_neg_pow_mul_from_18_to_21(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))) :
   n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  have sum_neg_cancel : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
    rw[Nat.sub_add_cancel zero_lt_n]
  rw[sum_neg_cancel]
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  simp

theorem sum_neg_pow_mul_from_19_to_19(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(sum_neg_cancel :  ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(gol:  n = 0 ∨ ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  rw[sum_neg_cancel]
  apply gol

theorem sum_neg_pow_mul_from_19_to_20(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(sum_neg_cancel :  ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(gol:  n = 0 ∨ 0 = 0) :
   n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  rw[sum_neg_cancel]
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  apply gol

theorem sum_neg_pow_mul_from_19_to_21(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(sum_neg_cancel :  ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)) :
   n = 0 ∨ ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  rw[sum_neg_cancel]
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  simp

theorem sum_neg_pow_mul_from_20_to_20(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(sum_neg_cancel :  ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(gol:  n = 0 ∨ 0 = 0) :
   n = 0 ∨ ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  apply gol

theorem sum_neg_pow_mul_from_20_to_21(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(sum_neg_cancel :  ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)) :
   n = 0 ∨ ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  rw[Int.alternating_sum_range_choose_of_ne n_sub_one]
  simp

theorem sum_neg_pow_mul_from_21_to_21(n : ℕ)(hn : 1 < n)(zero_lt_n : 0 < n)(n_sub_one : n - 1 ≠ 0)(hk :  ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k))(neg_pow_mul_choose_mul_eq_mul_sub :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_cancel :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)))(neg_pow_mul_mul_mul :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (k - 1)) =    ∑ k in Ico 1 (n + 1), -1 * ((-1 : ℝ) ^ (k - 1) * ↑n * ↑(Nat.choose (n - 1) (k - 1))))(sum_neg_comm :  ∑ x in range n, (-1 : ℝ) ^ x * ↑n * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x))(sum_neg_assoc :  ∑ x in range n, ↑n * (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range n, ↑n * ((-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)))(sum_neg_cancel :  ∑ x in range n, (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x)) :
   n = 0 ∨ 0 = 0 := by
  simp

