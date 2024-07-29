import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem sum_neg_pow_mul_mul_choose : ∑ k in range (n+1), (-1 : ℤ)^k * k * (choose n k)  = (-1 : ℤ)^0 * 0 * (choose n 0) + ∑ k in Ico 1 (n+1), (-1 : ℤ)^k * k * (choose n k) := by
    rw[range_eq_Ico]
    have n_succ: 0 < n + 1 := by linarith
    rw[sum_eq_sum_Ico_succ_bot n_succ]
    simp


theorem sum_neg_pow_mul_mul_choose_from_0_to_0(n : ℕ)(gol:  ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) := by
  rw[range_eq_Ico]
  apply gol

theorem sum_neg_pow_mul_mul_choose_from_0_to_1(n : ℕ)(gol:  ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) := by
  rw[range_eq_Ico]
  have n_succ: 0 < n + 1 := by linarith
  apply gol

theorem sum_neg_pow_mul_mul_choose_from_0_to_2(n : ℕ)(gol:  (-1 : ℝ) ^ 0 * ↑0 * ↑(Nat.choose n 0) + ∑ k in Ico (0 + 1) (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) := by
  rw[range_eq_Ico]
  have n_succ: 0 < n + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot n_succ]
  apply gol

theorem sum_neg_pow_mul_mul_choose_from_0_to_3(n : ℕ) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) := by
  rw[range_eq_Ico]
  have n_succ: 0 < n + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot n_succ]
  simp

theorem sum_neg_pow_mul_mul_choose_from_1_to_1(n : ℕ)(gol:  ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k)) :
   ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) := by
  have n_succ: 0 < n + 1 := by linarith
  apply gol

theorem sum_neg_pow_mul_mul_choose_from_1_to_2(n : ℕ)(gol:  (-1 : ℝ) ^ 0 * ↑0 * ↑(Nat.choose n 0) + ∑ k in Ico (0 + 1) (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k)) :
   ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) := by
  have n_succ: 0 < n + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot n_succ]
  apply gol

theorem sum_neg_pow_mul_mul_choose_from_1_to_3(n : ℕ) :
   ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) := by
  have n_succ: 0 < n + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot n_succ]
  simp

theorem sum_neg_pow_mul_mul_choose_from_2_to_2(n : ℕ)(n_succ : 0 < n + 1)(gol:  (-1 : ℝ) ^ 0 * ↑0 * ↑(Nat.choose n 0) + ∑ k in Ico (0 + 1) (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k)) :
   ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) := by
  rw[sum_eq_sum_Ico_succ_bot n_succ]
  apply gol

theorem sum_neg_pow_mul_mul_choose_from_2_to_3(n : ℕ)(n_succ : 0 < n + 1) :
   ∑ k in Ico 0 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) := by
  rw[sum_eq_sum_Ico_succ_bot n_succ]
  simp

theorem sum_neg_pow_mul_mul_choose_from_3_to_3(n : ℕ)(n_succ : 0 < n + 1) :
   (-1 : ℝ) ^ 0 * ↑0 * ↑(Nat.choose n 0) + ∑ k in Ico (0 + 1) (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) =
    (-1 : ℝ) ^ 0 * 0 * ↑(Nat.choose n 0) + ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑k * ↑(Nat.choose n k) := by
  simp

