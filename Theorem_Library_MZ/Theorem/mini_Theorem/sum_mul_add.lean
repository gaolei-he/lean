import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators


theorem sum_mul_add {n : ℕ} : ∑ k in Ico 1 (n + 1), k * (choose (2*n) k + choose (2*n) (k-1))
                  = ∑ k in Ico 1 (n + 1), (k * choose (2*n) k + k * choose (2*n) (k-1)) := by
  refine' sum_congr rfl fun k hk => _
  rw [mul_add]
