import Theorem.example_separate.pow_mul_choose

open Nat

open Finset

open BigOperators

theorem Ico_pow_mul_choose :   --sum41
  ∑ k in Ico 1 (n + 1), k ^ 2 * choose n k = n * ∑ k in Ico 1 (n + 1), k * choose (n-1) (k-1)  := by
    rw[mul_sum]
    refine' sum_congr rfl fun y hy ↦ _
    have hyn : y ≤ n := by
      have yn_succ : y < n + 1 := by exact (mem_Ico.1 hy).2
      exact Nat.le_of_lt_succ yn_succ
    have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[pow_mul_choose (hyn) (hy1)]
    rw[mul_assoc]
