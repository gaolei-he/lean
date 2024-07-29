import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators


theorem sum_range_succ_eq_sum_range : ∑ k in range (n+1), (k * choose (2 * n) k) = (2 * n) * ∑ k in range n, (choose (2*n - 1) k) := by
  rw[range_eq_Ico]
  have h01: 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h01]
  simp
  have h1: ∑ k in Ico 1 (n+1), k * (choose (2 * n) k) = ∑ k in Ico 1 (n+1), (2 * n) * (choose (2*n - 1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
    have hkn: y ≤ 2 * n := by linarith
    have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[choose_mul_eq_mul_sub' hkn hsk]
  rw[h1]
  rw[mul_sum] -- 提出 2 * n + 1
  rw[sum_Ico_eq_sum_range] -- 代换 l = k - 1
  simp --∑ k in range (n+1), (k * choose (2 * n) k) = (2 * n) * ∑ k in range n, (choose (2*n - 1) k)
