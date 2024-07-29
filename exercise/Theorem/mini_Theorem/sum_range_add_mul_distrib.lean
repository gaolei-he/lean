import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators


theorem sum_range_add_mul_distrib {n : ℕ} : ∑ k in range (n+1), (k+1) * choose (2*n) k
          = ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k := by
  rw [←sum_add_distrib]
  refine' sum_congr rfl fun k hk => _
  rw [add_mul]
  simp
