import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem ite_merge {n : ℕ} : ∑ k in range (n+1), ((if k % 2 = 1 then choose n k - (-1)^k * choose n k else choose n k - (-1)^k * choose n k) : ℤ)
                = ∑ k in range (n+1), ((choose n k - (-1)^k * choose n k) : ℤ) := by simp
