import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by   -- 更改 k 的范围
  rw[range_eq_Ico]
  have h_succ : 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h_succ]
  simp


theorem range_eq_ico_mul_choose_from_0_to_0(n : ℕ)(gol:  ∑ k in Ico 0 (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k) :
   ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k := by
  rw[range_eq_Ico]
  apply gol

theorem range_eq_ico_mul_choose_from_0_to_1(n : ℕ)(gol:  ∑ k in Ico 0 (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k) :
   ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k := by
  rw[range_eq_Ico]
  have h_succ : 0 < n + 1 := by linarith
  apply gol

theorem range_eq_ico_mul_choose_from_0_to_2(n : ℕ)(gol:  0 * Nat.choose n 0 + ∑ k in Ico (0 + 1) (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k) :
   ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k := by
  rw[range_eq_Ico]
  have h_succ : 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h_succ]
  apply gol

theorem range_eq_ico_mul_choose_from_0_to_3(n : ℕ) :
   ∑ k in range (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k := by
  rw[range_eq_Ico]
  have h_succ : 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h_succ]
  simp

theorem range_eq_ico_mul_choose_from_1_to_1(n : ℕ)(gol:  ∑ k in Ico 0 (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k) :
   ∑ k in Ico 0 (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k := by
  have h_succ : 0 < n + 1 := by linarith
  apply gol

theorem range_eq_ico_mul_choose_from_1_to_2(n : ℕ)(gol:  0 * Nat.choose n 0 + ∑ k in Ico (0 + 1) (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k) :
   ∑ k in Ico 0 (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k := by
  have h_succ : 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h_succ]
  apply gol

theorem range_eq_ico_mul_choose_from_1_to_3(n : ℕ) :
   ∑ k in Ico 0 (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k := by
  have h_succ : 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h_succ]
  simp

theorem range_eq_ico_mul_choose_from_2_to_2(n : ℕ)(h_succ : 0 < n + 1)(gol:  0 * Nat.choose n 0 + ∑ k in Ico (0 + 1) (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k) :
   ∑ k in Ico 0 (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k := by
  rw [sum_eq_sum_Ico_succ_bot h_succ]
  apply gol

theorem range_eq_ico_mul_choose_from_2_to_3(n : ℕ)(h_succ : 0 < n + 1) :
   ∑ k in Ico 0 (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k := by
  rw [sum_eq_sum_Ico_succ_bot h_succ]
  simp

theorem range_eq_ico_mul_choose_from_3_to_3(n : ℕ)(h_succ : 0 < n + 1) :
   0 * Nat.choose n 0 + ∑ k in Ico (0 + 1) (n + 1), k * Nat.choose n k = ∑ k in Ico 1 (n + 1), k * Nat.choose n k := by
  simp

