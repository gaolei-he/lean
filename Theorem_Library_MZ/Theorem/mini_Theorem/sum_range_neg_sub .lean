import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_range_neg_sub {n : ℕ} : ∑ k in range (n+1), -(k-(n:ℝ)) * choose (2*n) k
                  = ∑ k in range (n+1), ((n:ℝ)-k) * choose (2*n) k := by
  refine' sum_congr rfl fun k hk => _
  congr 1
  exact neg_sub (k:ℝ) (n:ℝ)
