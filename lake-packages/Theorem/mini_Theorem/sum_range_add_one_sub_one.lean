import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_range_add_one_sub_one {n : ℕ} : (-1 : ℝ) * ∑ k in range (n+1), ((n:ℝ)-k-n) * choose (2*n) (n-k)
      = (-1 : ℝ) * ∑ k in range (n + 1), ((n + 1 - 1 - k) - n) * ((Nat.choose (2 * n) (n + 1 - 1 - k)) : ℝ) := by
  congr 1
  refine' sum_congr rfl fun k hk => _
  congr 1
  simp
