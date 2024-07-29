import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem sum_range_choose_mul_eq (n : ℕ) : ∑ k in range (n+1), k * choose (2*n) k = n * 2^(2*n-1) := by sorry
