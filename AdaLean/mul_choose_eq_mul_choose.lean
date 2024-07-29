import AdaLean.choose_mul_eq_mul_sub'
import AdaLean.range_eq_ico_mul_choose

open Nat

open Finset

open BigOperators

theorem mul_choose_eq_mul_choose(hn :0 < n) : ∑ k in range (n+1), k * choose n k = ∑ k in Ico 1 (n + 1), n * choose (n-1) (k-1) := by
  rw[range_eq_ico_mul_choose]
  refine' sum_congr rfl fun y hy => _
  have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
  have hyn : y ≤ n := by
    have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
    linarith
  rw[choose_mul_eq_mul_sub' hyn hy1]  -- 使用定理1.3
