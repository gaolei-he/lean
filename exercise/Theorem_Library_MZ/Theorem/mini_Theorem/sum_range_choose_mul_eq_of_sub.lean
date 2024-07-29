import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Theorem.mini_Theorem.sum_range_choose_mul_eq

open Nat
open Finset
open BigOperators


theorem sum_range_choose_mul_eq_of_sub {n : ℕ} : (∑ k in range (n+1), n * choose (2*n) k) - (∑ k in range (n+1), k * choose (2*n) k)
                  = ∑ k in range (n+1), n * choose (2*n) k - ((n * 2^(2*n-1)) :ℕ) := by
  congr 1
  rw [sum_range_choose_mul_eq n]
