import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat

open Finset

open BigOperators


theorem Ico_simpn (hn : 1 ≤ n): ∑ k in Ico 1 (n+1), (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ)) =
   ∑ k in Ico 1 n, (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ) ) := by
    rw [sum_Ico_succ_top hn]
    simp
