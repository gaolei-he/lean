import Mathlib.Data.Real.Basic
import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators


theorem Ico_div : 1 / (2 * m + 1) * ∑ k in Ico 1 (2 * m + 1), k * (-1 : ℝ ) ^ k / choose (2 * m) (k-1) = 1 / (2 * m + 1) * ∑ l in Ico 0 (2 * m), (l+1) * (-1 : ℝ ) ^ (l+1) / choose (2 * m) l := by
  rw[sum_Ico_eq_sum_range]
  simp
  rw[range_eq_Ico]
  apply Or.inl
  refine' sum_congr rfl fun y _ => _
  rw[add_comm]
  congr 2
  rw[add_comm]


theorem Ico_div_from_0_to_0(m : ℕ)(gol:  1 / (2 * ↑m + 1) * ∑ k in range (2 * m + 1 - 1), ↑(1 + k) * (-1 : ℝ) ^ (1 + k) / ↑(Nat.choose (2 * m) (1 + k - 1)) =
    1 / (2 * ↑m + 1) * ∑ l in Ico 0 (2 * m), (↑l + 1) * (-1 : ℝ) ^ (l + 1) / ↑(Nat.choose (2 * m) l)) :
   1 / (2 * ↑m + 1) * ∑ k in Ico 1 (2 * m + 1), ↑k * (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) (k - 1)) =
    1 / (2 * ↑m + 1) * ∑ l in Ico 0 (2 * m), (↑l + 1) * (-1 : ℝ) ^ (l + 1) / ↑(Nat.choose (2 * m) l) := by
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem Ico_div_from_0_to_1(m : ℕ)(gol:  ∑ x in range (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
      ∑ x in range (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x) ∨
    2 * ↑m + 1 = 0) :
   1 / (2 * ↑m + 1) * ∑ k in Ico 1 (2 * m + 1), ↑k * (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) (k - 1)) =
    1 / (2 * ↑m + 1) * ∑ l in Ico 0 (2 * m), (↑l + 1) * (-1 : ℝ) ^ (l + 1) / ↑(Nat.choose (2 * m) l) := by
  rw[sum_Ico_eq_sum_range]
  simp
  apply gol

theorem Ico_div_from_0_to_2(m : ℕ)(gol:  ∑ x in Ico 0 (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
      ∑ x in Ico 0 (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x) ∨
    2 * ↑m + 1 = 0) :
   1 / (2 * ↑m + 1) * ∑ k in Ico 1 (2 * m + 1), ↑k * (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) (k - 1)) =
    1 / (2 * ↑m + 1) * ∑ l in Ico 0 (2 * m), (↑l + 1) * (-1 : ℝ) ^ (l + 1) / ↑(Nat.choose (2 * m) l) := by
  rw[sum_Ico_eq_sum_range]
  simp
  rw[range_eq_Ico]
  apply gol

theorem Ico_div_from_0_to_3(m : ℕ)(gol:  ∑ x in Ico 0 (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
    ∑ x in Ico 0 (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x)) :
   1 / (2 * ↑m + 1) * ∑ k in Ico 1 (2 * m + 1), ↑k * (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) (k - 1)) =
    1 / (2 * ↑m + 1) * ∑ l in Ico 0 (2 * m), (↑l + 1) * (-1 : ℝ) ^ (l + 1) / ↑(Nat.choose (2 * m) l) := by
  rw[sum_Ico_eq_sum_range]
  simp
  rw[range_eq_Ico]
  apply Or.inl
  apply gol

theorem Ico_div_from_1_to_1(m : ℕ)(gol:  ∑ x in range (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
      ∑ x in range (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x) ∨
    2 * ↑m + 1 = 0) :
   1 / (2 * ↑m + 1) * ∑ k in range (2 * m + 1 - 1), ↑(1 + k) * (-1 : ℝ) ^ (1 + k) / ↑(Nat.choose (2 * m) (1 + k - 1)) =
    1 / (2 * ↑m + 1) * ∑ l in Ico 0 (2 * m), (↑l + 1) * (-1 : ℝ) ^ (l + 1) / ↑(Nat.choose (2 * m) l) := by
  simp
  apply gol

theorem Ico_div_from_1_to_2(m : ℕ)(gol:  ∑ x in Ico 0 (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
      ∑ x in Ico 0 (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x) ∨
    2 * ↑m + 1 = 0) :
   1 / (2 * ↑m + 1) * ∑ k in range (2 * m + 1 - 1), ↑(1 + k) * (-1 : ℝ) ^ (1 + k) / ↑(Nat.choose (2 * m) (1 + k - 1)) =
    1 / (2 * ↑m + 1) * ∑ l in Ico 0 (2 * m), (↑l + 1) * (-1 : ℝ) ^ (l + 1) / ↑(Nat.choose (2 * m) l) := by
  simp
  rw[range_eq_Ico]
  apply gol

theorem Ico_div_from_1_to_3(m : ℕ)(gol:  ∑ x in Ico 0 (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
    ∑ x in Ico 0 (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x)) :
   1 / (2 * ↑m + 1) * ∑ k in range (2 * m + 1 - 1), ↑(1 + k) * (-1 : ℝ) ^ (1 + k) / ↑(Nat.choose (2 * m) (1 + k - 1)) =
    1 / (2 * ↑m + 1) * ∑ l in Ico 0 (2 * m), (↑l + 1) * (-1 : ℝ) ^ (l + 1) / ↑(Nat.choose (2 * m) l) := by
  simp
  rw[range_eq_Ico]
  apply Or.inl
  apply gol

theorem Ico_div_from_2_to_2(m : ℕ)(gol:  ∑ x in Ico 0 (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
      ∑ x in Ico 0 (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x) ∨
    2 * ↑m + 1 = 0) :
   ∑ x in range (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
      ∑ x in range (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x) ∨
    2 * ↑m + 1 = 0 := by
  rw[range_eq_Ico]
  apply gol

theorem Ico_div_from_2_to_3(m : ℕ)(gol:  ∑ x in Ico 0 (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
    ∑ x in Ico 0 (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x)) :
   ∑ x in range (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
      ∑ x in range (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x) ∨
    2 * ↑m + 1 = 0 := by
  rw[range_eq_Ico]
  apply Or.inl
  apply gol

theorem Ico_div_from_3_to_3(m : ℕ)(gol:  ∑ x in Ico 0 (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
    ∑ x in Ico 0 (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x)) :
   ∑ x in Ico 0 (2 * m), (1 + ↑x) * (-1 : ℝ) ^ (1 + x) / ↑(Nat.choose (2 * m) x) =
      ∑ x in Ico 0 (2 * m), (↑x + 1) * (-1 : ℝ) ^ (x + 1) / ↑(Nat.choose (2 * m) x) ∨
    2 * ↑m + 1 = 0 := by
  apply Or.inl
  apply gol

theorem Ico_div_from_5_to_5(m y : ℕ)(x✝ : y ∈ Ico 0 (2 * m))(gol:  (↑y + 1) * (-1 : ℝ) ^ (1 + y) / ↑(Nat.choose (2 * m) y) = (↑y + 1) * (-1 : ℝ) ^ (y + 1) / ↑(Nat.choose (2 * m) y)) :
   (1 + ↑y) * (-1 : ℝ) ^ (1 + y) / ↑(Nat.choose (2 * m) y) = (↑y + 1) * (-1 : ℝ) ^ (y + 1) / ↑(Nat.choose (2 * m) y) := by
  rw[add_comm]
  apply gol

theorem Ico_div_from_7_to_7(m y : ℕ)(x✝ : y ∈ Ico 0 (2 * m)) :
   (-1 : ℝ) ^ (1 + y) = (-1 : ℝ) ^ (y + 1) := by
  rw[add_comm]

