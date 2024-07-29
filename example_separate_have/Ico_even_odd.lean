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
  --
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
