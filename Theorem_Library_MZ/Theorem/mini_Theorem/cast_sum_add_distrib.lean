import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem cast_sum_add_distrib {n : ℕ} : ∑ k in range (n+1), ((n:ℝ) * choose (2*n) k - k * choose (2*n) k)
                = ∑ k in range (n+1), (n:ℝ) * choose (2*n) k - ∑ k in range (n+1), k * choose (2*n) k := by
  rw [sum_sub_distrib]
  congr 1
  rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n) x]
  refine' sum_congr rfl fun k hk => _
  rw [cast_mul]
