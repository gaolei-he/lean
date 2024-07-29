import Mathlib.Data.Real.Basic
import Theorem.example_separate.add_two_sub

open Nat

open Finset

open BigOperators

theorem Transit_item: ∑ k in Ico (2*n + 1 - n) (2 * n + 1 - 1), (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ)) =
        ∑ k in Ico (n+1) (2 * n), (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ)) := by
        rw[add_two_sub]
        simp
