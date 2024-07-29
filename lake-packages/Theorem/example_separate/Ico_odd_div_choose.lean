import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat

open Finset

open BigOperators

theorem Ico_odd_div_choose : ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ ) ^ k / choose (2 * m + 1) k = ∑ k in Ico 1 (2 * m + 1), k * (-1 : ℝ ) ^ k / (k * choose (2 * m + 1) k) := by
  refine' sum_congr rfl fun y hy => _
  have hy1 :  1 ≤ y := by exact (mem_Ico.1 hy).1
  have hy0 :  y ≠  0 := by linarith
  have hy : (y : ℝ) ≠ 0 := by
    simp
    exact hy0
  rw[mul_div_mul_left]
  exact hy


theorem Ico_odd_div_choose_from_1_to_1(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(gol:  (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy1 :  1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_odd_div_choose_from_1_to_2(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(gol:  (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy1 :  1 ≤ y := by exact (mem_Ico.1 hy).1
  have hy0 :  y ≠  0 := by linarith
  apply gol

theorem Ico_odd_div_choose_from_1_to_3(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(gol:  (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy1 :  1 ≤ y := by exact (mem_Ico.1 hy).1
  have hy0 :  y ≠  0 := by linarith
  have hy : (y : ℝ) ≠ 0 := by
    simp
    exact hy0
  apply gol

theorem Ico_odd_div_choose_from_1_to_4(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(gol:  ↑y ≠ 0) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy1 :  1 ≤ y := by exact (mem_Ico.1 hy).1
  have hy0 :  y ≠  0 := by linarith
  have hy : (y : ℝ) ≠ 0 := by
    simp
    exact hy0
  rw[mul_div_mul_left]
  apply gol

theorem Ico_odd_div_choose_from_1_to_5(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1)) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy1 :  1 ≤ y := by exact (mem_Ico.1 hy).1
  have hy0 :  y ≠  0 := by linarith
  have hy : (y : ℝ) ≠ 0 := by
    simp
    exact hy0
  rw[mul_div_mul_left]
  exact hy

theorem Ico_odd_div_choose_from_2_to_2(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hy1 : 1 ≤ y)(gol:  (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy0 :  y ≠  0 := by linarith
  apply gol

theorem Ico_odd_div_choose_from_2_to_3(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hy1 : 1 ≤ y)(gol:  (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy0 :  y ≠  0 := by linarith
  have hy : (y : ℝ) ≠ 0 := by
    simp
    exact hy0
  apply gol

theorem Ico_odd_div_choose_from_2_to_4(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hy1 : 1 ≤ y)(gol:  ↑y ≠ 0) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy0 :  y ≠  0 := by linarith
  have hy : (y : ℝ) ≠ 0 := by
    simp
    exact hy0
  rw[mul_div_mul_left]
  apply gol

theorem Ico_odd_div_choose_from_2_to_5(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hy1 : 1 ≤ y) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy0 :  y ≠  0 := by linarith
  have hy : (y : ℝ) ≠ 0 := by
    simp
    exact hy0
  rw[mul_div_mul_left]
  exact hy

theorem Ico_odd_div_choose_from_3_to_3(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hy1 : 1 ≤ y)(hy0 : y ≠ 0)(gol:  (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy : (y : ℝ) ≠ 0 := by
    simp
    exact hy0
  apply gol

theorem Ico_odd_div_choose_from_3_to_4(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hy1 : 1 ≤ y)(hy0 : y ≠ 0)(gol:  ↑y ≠ 0) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy : (y : ℝ) ≠ 0 := by
    simp
    exact hy0
  rw[mul_div_mul_left]
  apply gol

theorem Ico_odd_div_choose_from_3_to_5(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hy1 : 1 ≤ y)(hy0 : y ≠ 0) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  have hy : (y : ℝ) ≠ 0 := by
    simp
    exact hy0
  rw[mul_div_mul_left]
  exact hy

theorem Ico_odd_div_choose_from_4_to_4(m y : ℕ)(hy✝ : y ∈ Ico 1 (2 * m + 1))(hy1 : 1 ≤ y)(hy0 : y ≠ 0)(hy : ↑y ≠ 0)(gol:  ↑y ≠ 0) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  rw[mul_div_mul_left]
  apply gol

theorem Ico_odd_div_choose_from_4_to_5(m y : ℕ)(hy✝ : y ∈ Ico 1 (2 * m + 1))(hy1 : 1 ≤ y)(hy0 : y ≠ 0)(hy : ↑y ≠ 0) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) := by
  rw[mul_div_mul_left]
  exact hy

theorem Ico_odd_div_choose_from_5_to_5(m y : ℕ)(hy✝ : y ∈ Ico 1 (2 * m + 1))(hy1 : 1 ≤ y)(hy0 : y ≠ 0)(hy : ↑y ≠ 0) :
   ↑y ≠ 0 := by
  exact hy

