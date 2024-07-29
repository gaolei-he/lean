import Theorem.mini_separate.succ_mul_choose_eq'

open Nat

open Finset

open BigOperators

theorem alternating_sum_mul_mul_choose {n : ℕ} (h0 : 1 < n): ∑ k in range (n+1), (-1 : ℤ)^k * k * choose n k = 0 := by
  rw [range_eq_Ico]
  have hzero_lt_n : 0 < n+1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot hzero_lt_n]
  simp [mul_assoc]
  have h1 : ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * (k * choose n k)
    = ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * (n * choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    rw [←cast_mul, ←cast_mul]
    rw [succ_mul_choose_eq' h0 (mem_Ico.mp hy).left]
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]


theorem alternating_sum_mul_mul_choose_from_0_to_0(n : ℕ)(h0 : 1 < n)(gol:  ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  rw [range_eq_Ico]
  apply gol

theorem alternating_sum_mul_mul_choose_from_0_to_1(n : ℕ)(h0 : 1 < n)(gol:  ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  rw [range_eq_Ico]
  have hzero_lt_n : 0 < n+1 := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_0_to_2(n : ℕ)(h0 : 1 < n)(gol:  (-1 : ℝ) ^ 0 * ↑0 * ↑(Nat.choose n 0) + ∑ k in Ico (0 + 1) (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  rw [range_eq_Ico]
  have hzero_lt_n : 0 < n+1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot hzero_lt_n]
  apply gol

theorem alternating_sum_mul_mul_choose_from_0_to_3(n : ℕ)(h0 : 1 < n)(gol:  ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  rw [range_eq_Ico]
  have hzero_lt_n : 0 < n+1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot hzero_lt_n]
  simp [mul_assoc]
  apply gol

theorem alternating_sum_mul_mul_choose_from_1_to_1(n : ℕ)(h0 : 1 < n)(gol:  ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  have hzero_lt_n : 0 < n+1 := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_1_to_2(n : ℕ)(h0 : 1 < n)(gol:  (-1 : ℝ) ^ 0 * ↑0 * ↑(Nat.choose n 0) + ∑ k in Ico (0 + 1) (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  have hzero_lt_n : 0 < n+1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot hzero_lt_n]
  apply gol

theorem alternating_sum_mul_mul_choose_from_1_to_3(n : ℕ)(h0 : 1 < n)(gol:  ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0) :
   ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  have hzero_lt_n : 0 < n+1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot hzero_lt_n]
  simp [mul_assoc]
  apply gol

theorem alternating_sum_mul_mul_choose_from_2_to_2(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(gol:  (-1 : ℝ) ^ 0 * ↑0 * ↑(Nat.choose n 0) + ∑ k in Ico (0 + 1) (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0) :
   ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  rw [sum_eq_sum_Ico_succ_bot hzero_lt_n]
  apply gol

theorem alternating_sum_mul_mul_choose_from_2_to_3(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(gol:  ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0) :
   ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  rw [sum_eq_sum_Ico_succ_bot hzero_lt_n]
  simp [mul_assoc]
  apply gol

theorem alternating_sum_mul_mul_choose_from_3_to_3(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(gol:  ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0) :
   (-1 : ℝ) ^ 0 * ↑0 * ↑(Nat.choose n 0) + ∑ k in Ico (0 + 1) (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) = 0 := by
  simp [mul_assoc]
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_5(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_6(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_7(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_8(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_9(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_10(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_11(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_12(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_13(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_14(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_15(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_5_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1)))) :
   ∑ x in Ico 1 (n + 1), (-1 : ℝ) ^ x * (↑x * ↑(Nat.choose n x)) = 0 := by
  rw [h1]
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_6_to_6(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_7(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_8(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_9(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_10(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_11(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_12(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_13(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_14(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_15(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_6_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1)))) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))) = 0 := by
  rw [sum_Ico_eq_sum_range]
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_7_to_7(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  apply gol

theorem alternating_sum_mul_mul_choose_from_7_to_8(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  apply gol

theorem alternating_sum_mul_mul_choose_from_7_to_9(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  apply gol

theorem alternating_sum_mul_mul_choose_from_7_to_10(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  apply gol

theorem alternating_sum_mul_mul_choose_from_7_to_11(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_7_to_12(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  apply gol

theorem alternating_sum_mul_mul_choose_from_7_to_13(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_7_to_14(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_7_to_15(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_7_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_7_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_7_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1)))) :
   ∑ k in range (n + 1 - 1), (-1 : ℝ) ^ (1 + k) * (↑n * ↑(Nat.choose (n - 1) (1 + k - 1))) = 0 := by
  simp [pow_add]
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_8_to_8(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  apply gol

theorem alternating_sum_mul_mul_choose_from_8_to_9(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  apply gol

theorem alternating_sum_mul_mul_choose_from_8_to_10(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  apply gol

theorem alternating_sum_mul_mul_choose_from_8_to_11(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_8_to_12(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  apply gol

theorem alternating_sum_mul_mul_choose_from_8_to_13(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_8_to_14(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_8_to_15(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_8_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_8_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_8_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1)))) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  have h2 : 0 < n-1 := tsub_pos_of_lt h0
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_9_to_9(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : 0 < n - 1)(gol:  ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  rw [pos_iff_ne_zero] at h2
  apply gol

theorem alternating_sum_mul_mul_choose_from_9_to_10(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : 0 < n - 1)(gol:  ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  apply gol

theorem alternating_sum_mul_mul_choose_from_9_to_11(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : 0 < n - 1)(gol:  n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_9_to_12(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : 0 < n - 1)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  apply gol

theorem alternating_sum_mul_mul_choose_from_9_to_13(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : 0 < n - 1)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_9_to_14(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : 0 < n - 1)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_9_to_15(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : 0 < n - 1)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_9_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : 0 < n - 1)(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_9_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : 0 < n - 1)(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_9_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : 0 < n - 1) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  rw [pos_iff_ne_zero] at h2
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_10_to_10(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  apply gol

theorem alternating_sum_mul_mul_choose_from_10_to_11(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_10_to_12(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  apply gol

theorem alternating_sum_mul_mul_choose_from_10_to_13(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_10_to_14(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_10_to_15(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_10_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_10_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_10_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0) :
   ∑ x in range n, (-1 : ℝ) ^ x * (↑n * ↑(Nat.choose (n - 1) x)) = 0 := by
  simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum]
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_11_to_11(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_11_to_12(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  simp
  apply Or.inr
  apply gol

theorem alternating_sum_mul_mul_choose_from_11_to_13(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_11_to_14(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_11_to_15(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_11_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_11_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_11_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0) :
   ↑n * ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  simp
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_12_to_12(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  apply Or.inr
  apply gol

theorem alternating_sum_mul_mul_choose_from_12_to_13(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_12_to_14(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_12_to_15(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_12_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_12_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_12_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0) :
   n = 0 ∨ ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  apply Or.inr
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_13_to_13(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have hone_le_one : 1 ≤ 1 := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_13_to_14(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_13_to_15(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_13_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_13_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_13_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_14_to_14(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have hone_le_n : 1 ≤ n := by linarith
  apply gol

theorem alternating_sum_mul_mul_choose_from_14_to_15(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_14_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_14_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_14_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have hone_le_n : 1 ≤ n := by linarith
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_15_to_15(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(hone_le_n : 1 ≤ n)(gol:  ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  apply gol

theorem alternating_sum_mul_mul_choose_from_15_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(hone_le_n : 1 ≤ n)(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_15_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(hone_le_n : 1 ≤ n)(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_15_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(hone_le_n : 1 ≤ n) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  have h3 : n - 1 + 1 = n := by
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_16_to_16(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(hone_le_n : 1 ≤ n)(h3 : n - 1 + 1 = n)(gol:  ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  rw [←h3]
  apply gol

theorem alternating_sum_mul_mul_choose_from_16_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(hone_le_n : 1 ≤ n)(h3 : n - 1 + 1 = n)(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  rw [←h3]
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_16_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(hone_le_n : 1 ≤ n)(h3 : n - 1 + 1 = n) :
   ∑ x in range n, ↑(Nat.choose (n - 1) x) * (-1 : ℝ) ^ x = 0 := by
  rw [←h3]
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_17_to_17(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(hone_le_n : 1 ≤ n)(h3 : n - 1 + 1 = n)(gol:  ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0) :
   ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0 := by
  simp [cast_comm]
  apply gol

theorem alternating_sum_mul_mul_choose_from_17_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(hone_le_n : 1 ≤ n)(h3 : n - 1 + 1 = n) :
   ∑ x in range (n - 1 + 1), ↑(Nat.choose (n - 1 + 1 - 1) x) * (-1 : ℝ) ^ x = 0 := by
  simp [cast_comm]
  rw [Int.alternating_sum_range_choose_of_ne h2]

theorem alternating_sum_mul_mul_choose_from_18_to_18(n : ℕ)(h0 : 1 < n)(hzero_lt_n : 0 < n + 1)(h1 :  ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑k * ↑(Nat.choose n k)) =    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * (↑n * ↑(Nat.choose (n - 1) (k - 1))))(h2 : n - 1 ≠ 0)(hone_le_one : 1 ≤ 1)(hone_le_n : 1 ≤ n)(h3 : n - 1 + 1 = n) :
   ∑ x in range (n - 1 + 1), (-1 : ℝ) ^ x * ↑(Nat.choose (n - 1) x) = 0 := by
  rw [Int.alternating_sum_range_choose_of_ne h2]

