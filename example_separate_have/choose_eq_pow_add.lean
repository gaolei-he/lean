import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem choose_eq_pow_add: ∑ k in range (n+1), ((choose (2*n) k) :ℝ) = 2 ^ ( 2 * n - 1 ) + ((choose ( 2 * n ) n / 2) :ℝ) := by sorry  --example2
