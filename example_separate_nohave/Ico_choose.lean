import Mathlib.Data.Real.Basic
import Theorem.example_separate.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators

theorem Ico_choose: ∑ k in Ico 1 (n+1), k * ((choose (2*n + 1) k):ℝ) = ∑ k in Ico 1 (n+1), (2 * n + 1) * ((choose (2*n) (k-1)):ℝ) := by
    refine' sum_congr rfl fun y hy => _
    have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
    have hkn: y ≤ 2 * n + 1 := by linarith
    have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[← cast_mul]
    rw[choose_mul_eq_mul_sub' hkn hsk]
    simp
