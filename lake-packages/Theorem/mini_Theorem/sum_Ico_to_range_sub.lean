import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators


theorem sum_Ico_to_range_sub {n : ℕ} : ∑ k in Ico 1 (n + 1), k * choose (2*n) (k-1)
          = ∑ k in range (n+1), (k+1) * choose (2*n) k - (n+1) * choose (2*n) n := by
  rw [sum_Ico_eq_sum_range, sum_range_succ]
  simp [add_comm]
