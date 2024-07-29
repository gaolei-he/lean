import Mathlib.Data.Real.Basic
import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem odd_choose_sum(hnm: n = 2 * m + 1): ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ ) ^ k / choose (2 * m + 1) k := by
  rw[hnm]
  rw[sum_range_succ]
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot hm2]
  norm_num


theorem odd_choose_sum_from_0_to_0(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  ∑ k in range (2 * m + 1 + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[hnm]
  apply gol

theorem odd_choose_sum_from_0_to_1(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  ∑ x in range (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[hnm]
  rw[sum_range_succ]
  apply gol

theorem odd_choose_sum_from_0_to_2(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[hnm]
  rw[sum_range_succ]
  rw[range_eq_Ico]
  apply gol

theorem odd_choose_sum_from_0_to_3(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[hnm]
  rw[sum_range_succ]
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  apply gol

theorem odd_choose_sum_from_0_to_4(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m + 1) 0) + ∑ k in Ico (0 + 1) (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[hnm]
  rw[sum_range_succ]
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot hm2]
  apply gol

theorem odd_choose_sum_from_0_to_5(n m : ℕ)(hnm : n = 2 * m + 1) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[hnm]
  rw[sum_range_succ]
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot hm2]
  norm_num

theorem odd_choose_sum_from_1_to_1(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  ∑ x in range (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ k in range (2 * m + 1 + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[sum_range_succ]
  apply gol

theorem odd_choose_sum_from_1_to_2(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ k in range (2 * m + 1 + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[sum_range_succ]
  rw[range_eq_Ico]
  apply gol

theorem odd_choose_sum_from_1_to_3(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ k in range (2 * m + 1 + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[sum_range_succ]
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  apply gol

theorem odd_choose_sum_from_1_to_4(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m + 1) 0) + ∑ k in Ico (0 + 1) (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ k in range (2 * m + 1 + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[sum_range_succ]
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot hm2]
  apply gol

theorem odd_choose_sum_from_1_to_5(n m : ℕ)(hnm : n = 2 * m + 1) :
   ∑ k in range (2 * m + 1 + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[sum_range_succ]
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot hm2]
  norm_num

theorem odd_choose_sum_from_2_to_2(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ x in range (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[range_eq_Ico]
  apply gol

theorem odd_choose_sum_from_2_to_3(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ x in range (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  apply gol

theorem odd_choose_sum_from_2_to_4(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m + 1) 0) + ∑ k in Ico (0 + 1) (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ x in range (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot hm2]
  apply gol

theorem odd_choose_sum_from_2_to_5(n m : ℕ)(hnm : n = 2 * m + 1) :
   ∑ x in range (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[range_eq_Ico]
  have hm2 : 0 < 2 * m + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot hm2]
  norm_num

theorem odd_choose_sum_from_3_to_3(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  have hm2 : 0 < 2 * m + 1 := by linarith
  apply gol

theorem odd_choose_sum_from_3_to_4(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m + 1) 0) + ∑ k in Ico (0 + 1) (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  have hm2 : 0 < 2 * m + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot hm2]
  apply gol

theorem odd_choose_sum_from_3_to_5(n m : ℕ)(hnm : n = 2 * m + 1) :
   ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  have hm2 : 0 < 2 * m + 1 := by linarith
  rw[sum_eq_sum_Ico_succ_bot hm2]
  norm_num

theorem odd_choose_sum_from_4_to_4(n m : ℕ)(hnm : n = 2 * m + 1)(hm2 : 0 < 2 * m + 1)(gol:  (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m + 1) 0) + ∑ k in Ico (0 + 1) (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k)) :
   ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[sum_eq_sum_Ico_succ_bot hm2]
  apply gol

theorem odd_choose_sum_from_4_to_5(n m : ℕ)(hnm : n = 2 * m + 1)(hm2 : 0 < 2 * m + 1) :
   ∑ x in Ico 0 (2 * m + 1), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m + 1) x) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  rw[sum_eq_sum_Ico_succ_bot hm2]
  norm_num

theorem odd_choose_sum_from_5_to_5(n m : ℕ)(hnm : n = 2 * m + 1)(hm2 : 0 < 2 * m + 1) :
   (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m + 1) 0) + ∑ k in Ico (0 + 1) (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) +
      (-1 : ℝ) ^ (2 * m + 1) / ↑(Nat.choose (2 * m + 1) (2 * m + 1)) =
    ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) := by
  norm_num

