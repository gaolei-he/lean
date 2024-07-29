import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem choose_eq_pow_add:
 ∑ k in range (n+1), ((choose (2*n) k) :ℝ) =
  2 ^ ( 2 * n - 1 ) + ((choose ( 2 * n ) n / 2) :ℝ) := by sorry  --example2


theorem choose_eq_pow_add_from_0_to_0(n : ℕ) :
   ∑ k in range (n + 1), ↑(Nat.choose (2 * n) k) = 2 ^ (2 * n - 1) + ↑(Nat.choose (2 * n) n) / 2 := by
  sorry

