import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators


theorem mul_sum_of_sub {n : ℕ} : ∑ k in range (n+1), n * choose (2*n) k - ((n * 2^(2*n-1)) :ℕ)
                  = n * ∑ k in range (n+1), choose (2*n) k - ((n * 2^(2*n-1)) :ℕ) := by
  congr 1
  rw [mul_sum]
