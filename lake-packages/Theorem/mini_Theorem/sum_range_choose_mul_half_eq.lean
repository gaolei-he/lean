import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat

open Finset

open BigOperators

theorem sum_range_choose_mul_half_eq (n : ℕ) : ∑ k in range (n+1), choose (2*n) k = 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n := by sorry
