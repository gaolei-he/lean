import Mathlib.Data.Real.Basic
import Theorem.example_separate.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators

theorem bot_sum_mul_congr : ∑ k in range (n+1), ((k * choose (2 * n + 1) k):ℝ) = (2 * n + 1) * ∑ k in range n, ((choose (2*n) k):ℝ) := by
  rw[range_eq_Ico]
  have h01: 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h01]  -- 提出 f 0
  simp
  have h1: ∑ k in Ico 1 (n+1), k * ((choose (2*n + 1) k):ℝ) = ∑ k in Ico 1 (n+1), (2 * n + 1) * ((choose (2*n) (k-1)):ℝ) := by
    refine' sum_congr rfl fun y hy => _
    have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
    have hkn: y ≤ 2 * n + 1 := by linarith
    have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[← cast_mul]
    rw[choose_mul_eq_mul_sub' hkn hsk]
    simp
  rw[h1]
  rw[mul_sum]  -- 提出 2 * n + 1
  rw[sum_Ico_eq_sum_range]  -- 代换 l = k - 1
  simp
