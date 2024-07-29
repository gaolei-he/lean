import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem two_mul_sum_ite {n : ℕ} : 2 * (∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) else 0))
        = ∑ k in range (n+1), (if k % 2 = 1 then 2 * ((choose n k) : ℤ) else 0) := by
        rw [mul_sum]
        refine' sum_congr rfl fun y hy => _
        rw [ite_mul_zero_right (y % 2 = 1) 2 ((Nat.choose n y) : ℤ)]
