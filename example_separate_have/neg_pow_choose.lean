import Theorem.example_separate.choose_eq_choose_add
import Mathlib.Data.Real.Basic


open Nat

open Finset

open BigOperators

theorem neg_pow_choose(h1:1 ≤ n):
  ∑ k in Ico 1 n, (-1 : ℝ) ^ k * (choose n k : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k : ℝ) + (choose (n-1) (k-1) : ℝ)) * (m / (m+k)) := by
    refine' sum_congr rfl fun y hy => _
    congr 1
    have hab: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[choose_eq_choose_add h1 hab]
    simp
