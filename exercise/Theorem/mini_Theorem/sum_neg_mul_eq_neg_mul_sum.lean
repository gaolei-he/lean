import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_neg_mul_eq_neg_mul_sum {n : ℕ} : ∑ k in range (n+1), (-1 : ℝ) * (n-k-n) * choose (2*n) (n-k)
        = (-1 : ℝ) * ∑ k in range (n+1), ((n:ℝ)-k-n) * choose (2*n) (n-k) := by
        rw [mul_sum]
        refine' sum_congr rfl fun k hk => _
        rw [mul_assoc]
