import Theorem.example_separate.add_div_two
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators


theorem two_even_congr(hnm: n = 2 * m)(hm : 0 < m) : ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / choose (2 * m) k := by
  rw[hnm]  -- 用 2 * m 替换 n
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  norm_num


theorem two_even_congr_from_0_to_0(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  ∑ k in range (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw[hnm]
  apply gol

theorem two_even_congr_from_0_to_1(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw[hnm]
  rw [sum_range_succ]
  apply gol

theorem two_even_congr_from_0_to_2(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw[hnm]
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  apply gol

theorem two_even_congr_from_0_to_3(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  ∑ x in Ico 0 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw[hnm]
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  apply gol

theorem two_even_congr_from_0_to_4(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m) 0) + ∑ k in Ico (0 + 1) (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) +
      (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw[hnm]
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  apply gol

theorem two_even_congr_from_0_to_5(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + 1 =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw[hnm]
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  apply gol

theorem two_even_congr_from_0_to_6(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  1 + 1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw[hnm]
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  apply gol

theorem two_even_congr_from_0_to_7(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = 2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw[hnm]
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  norm_num

theorem two_even_congr_from_1_to_1(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ k in range (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [sum_range_succ]
  apply gol

theorem two_even_congr_from_1_to_2(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ k in range (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  apply gol

theorem two_even_congr_from_1_to_3(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  ∑ x in Ico 0 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ k in range (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  apply gol

theorem two_even_congr_from_1_to_4(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m) 0) + ∑ k in Ico (0 + 1) (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) +
      (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ k in range (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  apply gol

theorem two_even_congr_from_1_to_5(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + 1 =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   ∑ k in range (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  apply gol

theorem two_even_congr_from_1_to_6(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  1 + 1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   ∑ k in range (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  apply gol

theorem two_even_congr_from_1_to_7(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m) :
   ∑ k in range (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [sum_range_succ]
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  norm_num

theorem two_even_congr_from_2_to_2(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  have h2m : 0 < 2 * m:= by linarith
  apply gol

theorem two_even_congr_from_2_to_3(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  ∑ x in Ico 0 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  apply gol

theorem two_even_congr_from_2_to_4(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m) 0) + ∑ k in Ico (0 + 1) (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) +
      (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  apply gol

theorem two_even_congr_from_2_to_5(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + 1 =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  apply gol

theorem two_even_congr_from_2_to_6(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  1 + 1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  apply gol

theorem two_even_congr_from_2_to_7(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m) :
   ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  have h2m : 0 < 2 * m:= by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  norm_num

theorem two_even_congr_from_3_to_3(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m)(gol:  ∑ x in Ico 0 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [range_eq_Ico]
  apply gol

theorem two_even_congr_from_3_to_4(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m)(gol:  (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m) 0) + ∑ k in Ico (0 + 1) (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) +
      (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  apply gol

theorem two_even_congr_from_3_to_5(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m)(gol:  1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + 1 =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  apply gol

theorem two_even_congr_from_3_to_6(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m)(gol:  1 + 1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  apply gol

theorem two_even_congr_from_3_to_7(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m) :
   ∑ x in range (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  norm_num

theorem two_even_congr_from_4_to_4(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m)(gol:  (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m) 0) + ∑ k in Ico (0 + 1) (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) +
      (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k)) :
   ∑ x in Ico 0 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [sum_eq_sum_Ico_succ_bot h2m]
  apply gol

theorem two_even_congr_from_4_to_5(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m)(gol:  1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + 1 =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   ∑ x in Ico 0 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  apply gol

theorem two_even_congr_from_4_to_6(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m)(gol:  1 + 1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   ∑ x in Ico 0 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  apply gol

theorem two_even_congr_from_4_to_7(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m) :
   ∑ x in Ico 0 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  rw [sum_eq_sum_Ico_succ_bot h2m]
  simp
  rw[add_comm, ← add_assoc]
  norm_num

theorem two_even_congr_from_5_to_5(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m)(gol:  1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + 1 =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m) 0) + ∑ k in Ico (0 + 1) (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) +
      (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  simp
  apply gol

theorem two_even_congr_from_5_to_6(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m)(gol:  1 + 1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m) 0) + ∑ k in Ico (0 + 1) (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) +
      (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  simp
  rw[add_comm, ← add_assoc]
  apply gol

theorem two_even_congr_from_5_to_7(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m) :
   (-1 : ℝ) ^ 0 / ↑(Nat.choose (2 * m) 0) + ∑ k in Ico (0 + 1) (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) +
      (-1 : ℝ) ^ (2 * m) / ↑(Nat.choose (2 * m) (2 * m)) =
    2 + ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) k) := by
  simp
  rw[add_comm, ← add_assoc]
  norm_num

theorem two_even_congr_from_6_to_6(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m)(gol:  1 + 1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x)) :
   1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + 1 =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) := by
  rw[add_comm, ← add_assoc]
  apply gol

theorem two_even_congr_from_6_to_7(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m) :
   1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) + 1 =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) := by
  rw[add_comm, ← add_assoc]
  norm_num

theorem two_even_congr_from_7_to_7(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(h2m : 0 < 2 * m) :
   1 + 1 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) =
    2 + ∑ x in Ico 1 (2 * m), (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) x) := by
  norm_num

