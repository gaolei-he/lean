import Theorem.example_separate.choose_mul_eq_mul_sub'
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Data.Real.Basic


open Nat

open Finset

open BigOperators

theorem Ico_even_odd: ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ ) ^ k / choose (2 * m + 1) k = 1 / (2 * m + 1) * ∑ k in Ico 1 (2 * m + 1), k * (-1 : ℝ ) ^ k / choose (2 * m) (k-1) := by  --第三个等式
  rw[mul_sum]  -- 改写目标右侧，将 1 / (2 * m + 1) 放入 ∑
  refine' sum_congr rfl fun y hy => _
  -- hk : 目标左侧分子分母同乘 k
  have hk :  (-1 : ℝ ) ^ y / choose (2 * m + 1) y = y * (-1 : ℝ ) ^ y / (y * choose (2 * m + 1) y) := by
    have hy1 :  1 ≤ y := by exact (mem_Ico.1 hy).1
    have hy0 :  y ≠ 0 := by linarith
    have hy : (y : ℝ) ≠ 0 := by
      simp
      exact hy0
    rw[mul_div_mul_left]  -- 核心定理
    exact hy
  rw[hk]
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]  -- 核心定理， 改写目标左侧式子的分母
  simp
  rw[← div_div]  -- 运用结合律，将目标左侧式子分母拆开
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp


theorem Ico_even_odd_from_0_to_0(m : ℕ)(gol:  ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) =
    ∑ x in Ico 1 (2 * m + 1), 1 / (2 * ↑m + 1) * (↑x * (-1 : ℝ) ^ x / ↑(Nat.choose (2 * m) (x - 1)))) :
   ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m + 1) k) =
    1 / (2 * ↑m + 1) * ∑ k in Ico 1 (2 * m + 1), ↑k * (-1 : ℝ) ^ k / ↑(Nat.choose (2 * m) (k - 1)) := by
  rw[mul_sum]
  apply gol

theorem Ico_even_odd_from_3_to_3(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  apply gol

theorem Ico_even_odd_from_3_to_4(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  rw[← cast_mul]
  apply gol

theorem Ico_even_odd_from_3_to_5(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  apply gol

theorem Ico_even_odd_from_3_to_6(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  apply gol

theorem Ico_even_odd_from_3_to_7(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_even_odd_from_3_to_8(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  apply gol

theorem Ico_even_odd_from_3_to_9(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  apply gol

theorem Ico_even_odd_from_3_to_10(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  apply gol

theorem Ico_even_odd_from_3_to_11(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  apply gol

theorem Ico_even_odd_from_3_to_12(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  apply gol

theorem Ico_even_odd_from_3_to_13(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  apply gol

theorem Ico_even_odd_from_3_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y))) :
   (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[hk]
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp

theorem Ico_even_odd_from_4_to_4(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← cast_mul]
  apply gol

theorem Ico_even_odd_from_4_to_5(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  apply gol

theorem Ico_even_odd_from_4_to_6(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  apply gol

theorem Ico_even_odd_from_4_to_7(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_even_odd_from_4_to_8(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  apply gol

theorem Ico_even_odd_from_4_to_9(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  apply gol

theorem Ico_even_odd_from_4_to_10(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  apply gol

theorem Ico_even_odd_from_4_to_11(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  apply gol

theorem Ico_even_odd_from_4_to_12(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  apply gol

theorem Ico_even_odd_from_4_to_13(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  apply gol

theorem Ico_even_odd_from_4_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y))) :
   ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← cast_mul]
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp

theorem Ico_even_odd_from_5_to_5(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  apply gol

theorem Ico_even_odd_from_5_to_6(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  apply gol

theorem Ico_even_odd_from_5_to_7(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_even_odd_from_5_to_8(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  apply gol

theorem Ico_even_odd_from_5_to_9(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  apply gol

theorem Ico_even_odd_from_5_to_10(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  apply gol

theorem Ico_even_odd_from_5_to_11(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  apply gol

theorem Ico_even_odd_from_5_to_12(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  apply gol

theorem Ico_even_odd_from_5_to_13(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(gol:  1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  apply gol

theorem Ico_even_odd_from_5_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_lt_succ : y < 2 * m + 1 := by exact (mem_Ico.1 hy).2
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp

theorem Ico_even_odd_from_6_to_6(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  apply gol

theorem Ico_even_odd_from_6_to_7(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_even_odd_from_6_to_8(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(gol:  ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  apply gol

theorem Ico_even_odd_from_6_to_9(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(gol:  ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  apply gol

theorem Ico_even_odd_from_6_to_10(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  apply gol

theorem Ico_even_odd_from_6_to_11(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  apply gol

theorem Ico_even_odd_from_6_to_12(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(gol:  1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  apply gol

theorem Ico_even_odd_from_6_to_13(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(gol:  1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  apply gol

theorem Ico_even_odd_from_6_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_le_succ : y ≤ 2 * m + 1 := by linarith
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp

theorem Ico_even_odd_from_7_to_7(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(gol:  ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_even_odd_from_7_to_8(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(gol:  ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  apply gol

theorem Ico_even_odd_from_7_to_9(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(gol:  ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  apply gol

theorem Ico_even_odd_from_7_to_10(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  apply gol

theorem Ico_even_odd_from_7_to_11(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  apply gol

theorem Ico_even_odd_from_7_to_12(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(gol:  1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  apply gol

theorem Ico_even_odd_from_7_to_13(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(gol:  1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  apply gol

theorem Ico_even_odd_from_7_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have hy_1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp

theorem Ico_even_odd_from_8_to_8(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  apply gol

theorem Ico_even_odd_from_8_to_9(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  apply gol

theorem Ico_even_odd_from_8_to_10(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  apply gol

theorem Ico_even_odd_from_8_to_11(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  apply gol

theorem Ico_even_odd_from_8_to_12(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  apply gol

theorem Ico_even_odd_from_8_to_13(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  apply gol

theorem Ico_even_odd_from_8_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y) :
   ↑y * (-1 : ℝ) ^ y / ↑(y * Nat.choose (2 * m + 1) y) = 1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[choose_mul_eq_mul_sub' hy_le_succ hy_1]
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp

theorem Ico_even_odd_from_9_to_9(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  simp
  apply gol

theorem Ico_even_odd_from_9_to_10(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  simp
  rw[← div_div]
  apply gol

theorem Ico_even_odd_from_9_to_11(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  apply gol

theorem Ico_even_odd_from_9_to_12(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  apply gol

theorem Ico_even_odd_from_9_to_13(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  apply gol

theorem Ico_even_odd_from_9_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y) :
   ↑y * (-1 : ℝ) ^ y / ↑((2 * m + 1) * Nat.choose (2 * m + 1 - 1) (y - 1)) =
    1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  simp
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp

theorem Ico_even_odd_from_10_to_10(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← div_div]
  apply gol

theorem Ico_even_odd_from_10_to_11(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  apply gol

theorem Ico_even_odd_from_10_to_12(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  apply gol

theorem Ico_even_odd_from_10_to_13(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  apply gol

theorem Ico_even_odd_from_10_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y) :
   ↑y * (-1 : ℝ) ^ y / ((2 * ↑m + 1) * ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[← div_div]
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp

theorem Ico_even_odd_from_11_to_11(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  apply gol

theorem Ico_even_odd_from_11_to_12(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  apply gol

theorem Ico_even_odd_from_11_to_13(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  apply gol

theorem Ico_even_odd_from_11_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y) :
   ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  have inv_2m_add{k : ℕ} : k * (-1 : ℝ ) ^ k /(2 * m + 1) = (1 / (2 * m + 1)) * k * (-1 : ℝ ) ^ k := by
    rw[div_eq_mul_one_div]
    rw[mul_comm, mul_assoc]
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp

theorem Ico_even_odd_from_12_to_12(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[inv_2m_add]
  apply gol

theorem Ico_even_odd_from_12_to_13(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  apply gol

theorem Ico_even_odd_from_12_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y) :
   ↑y * (-1 : ℝ) ^ y / (2 * ↑m + 1) / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[inv_2m_add]
  rw[mul_assoc, ← mul_div]
  simp

theorem Ico_even_odd_from_13_to_13(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y)(gol:  1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)))) :
   1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[mul_assoc, ← mul_div]
  apply gol

theorem Ico_even_odd_from_13_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y) :
   1 / (2 * ↑m + 1) * ↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1)) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  rw[mul_assoc, ← mul_div]
  simp

theorem Ico_even_odd_from_14_to_14(m y : ℕ)(hy : y ∈ Ico 1 (2 * m + 1))(hk : (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m + 1) y) = ↑y * (-1 : ℝ) ^ y / (↑y * ↑(Nat.choose (2 * m + 1) y)))(hy_lt_succ : y < 2 * m + 1)(hy_le_succ : y ≤ 2 * m + 1)(hy_1 : 1 ≤ y) :
   1 / (2 * ↑m + 1) * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) =
    (2 * ↑m + 1)⁻¹ * (↑y * (-1 : ℝ) ^ y / ↑(Nat.choose (2 * m) (y - 1))) := by
  simp

