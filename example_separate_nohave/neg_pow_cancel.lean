import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem neg_pow_cancel : ∑ k in Ico 1 (n + 1), (-1 : ℤ) ^ k * n * (choose (n-1) (k-1)) =  ∑ k in Ico 1 (n + 1), (-1) ^ (k - 1) * (-1 : ℤ)* n * (choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hnegy : (-1 : ℤ ) ^ y = (-1) ^ (y - 1 + 1)  := by
      rw[Nat.sub_add_cancel hy1]
    congr 2
