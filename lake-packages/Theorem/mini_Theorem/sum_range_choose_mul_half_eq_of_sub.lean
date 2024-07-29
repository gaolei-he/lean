import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Theorem.mini_Theorem.sum_range_choose_mul_half_eq


open Nat
open Finset
open BigOperators


theorem sum_range_choose_mul_half_eq_of_sub {n : ℕ} : n * ∑ k in range (n+1), choose (2*n) k - ((n * 2^(2*n-1)) :ℕ)
                  = n * ((2^(2*n-1)) + (((1/2):ℝ) * choose (2*n) n)) - ((n * 2^(2*n-1)) :ℕ) := by
  congr 2
  rw [sum_range_choose_mul_half_eq n]
