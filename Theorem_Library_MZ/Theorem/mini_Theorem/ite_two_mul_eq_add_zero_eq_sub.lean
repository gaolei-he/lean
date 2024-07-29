import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem ite_two_mul_eq_add_zero_eq_sub {n : ℕ} : ∑ k in range (n+1), (if k % 2 = 1 then 2 * ((choose n k) : ℤ) else 0)
        = ∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) + ((choose n k) : ℤ) else ((choose n k) : ℤ) - ((choose n k) : ℤ)) := by
        refine' sum_congr rfl fun y hy => _
        congr 1
        rw [two_mul]
        simp
