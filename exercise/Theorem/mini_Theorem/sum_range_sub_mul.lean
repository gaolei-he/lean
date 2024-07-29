import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_range_sub_mul {n : ℕ} : ∑ k in range (n+1), ((n:ℝ)-k) * choose (2*n) k
                  = ∑ k in range (n+1), ((n:ℝ) * choose (2*n) k - k * choose (2*n) k) := by
  refine' sum_congr rfl fun k hk => _
  rw [sub_mul]
