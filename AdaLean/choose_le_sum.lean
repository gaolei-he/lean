import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators


theorem choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
      rw[sum_range_succ]
      simp
