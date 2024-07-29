import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators



theorem Ico_eq_range_with_add_zero_and_sub {n : ℕ} : ((∑ k in Ico 1 (n + 1), k * choose (2*n) k + ∑ k in Ico 1 (n + 1), k * choose (2*n) (k-1)) : ℝ)
    = ∑ k in range (n+1), k * choose (2*n) k
      + ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k - (n+(1:ℕ)) * choose (2*n) n := by
  rw [sum_Ico_to_range_add_zero, sum_Ico_to_range_sub]
  rw [cast_sub, ←add_sub_assoc]
  congr 1
  rw [add_assoc]
  congr 1
  rw [sum_range_add_mul_distrib, cast_add]
  rw [←cast_add, ←cast_mul]
  rw [sum_range_succ]
  have : 0 ≤ ∑ k in range n, (k + 1) * Nat.choose (2 * n) k := by
    exact Nat.zero_le (∑ k in range n, (k + 1) * Nat.choose (2 * n) k)
  linarith
