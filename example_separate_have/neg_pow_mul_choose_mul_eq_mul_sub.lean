import Theorem.example_separate.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators

theorem neg_pow_mul_choose_mul_eq_mul_sub:  ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * k * (choose n k) = ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * n * (choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hyn : y ≤ n := by
      have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
      linarith
    rw[mul_assoc, mul_assoc]
    congr 1
    rw[← cast_mul,← cast_mul]
    rw[choose_mul_eq_mul_sub' hyn hy1]
