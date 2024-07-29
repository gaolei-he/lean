import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem neg_mul_sum_eq_sum_neg_mul {n : ℕ} : (-1 : ℝ) * ∑ k in range (n+1), (k-(n:ℝ)) * choose (2*n) k
                  = ∑ k in range (n+1), -(k-(n:ℝ)) * choose (2*n) k := by
  rw [mul_sum]
  refine' sum_congr rfl fun k hk => _
  rw [←neg_one_mul (k-(n:ℝ))]
  rw [mul_assoc]
