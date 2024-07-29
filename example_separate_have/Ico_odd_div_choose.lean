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
