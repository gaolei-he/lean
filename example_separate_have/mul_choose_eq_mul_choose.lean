import Theorem.example_separate.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators

theorem mul_choose_eq_mul_choose(hn :0 < n) : ∑ k in range (n+1), k * choose n k = ∑ k in Ico 1 (n + 1), n * choose (n-1) (k-1) := by
  have range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by   -- 更改 k 的范围
    rw[range_eq_Ico]
    have h_succ : 0 < n + 1 := by linarith
    rw [sum_eq_sum_Ico_succ_bot h_succ]
    simp
  rw[range_eq_ico_mul_choose]
  refine' sum_congr rfl fun y hy => _
  have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
  have hyn : y ≤ n := by
    have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
    linarith
  rw[choose_mul_eq_mul_sub' hyn hy1]  -- 使用定理1.3
