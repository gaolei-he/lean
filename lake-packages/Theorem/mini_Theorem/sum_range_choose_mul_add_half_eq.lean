import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Theorem.mini_Theorem.sum_range_choose_mul_eq
import Theorem.mini_Theorem.sum_range_choose_mul_half_eq

open Nat
open Finset
open BigOperators


theorem sum_range_choose_mul_add_half_eq {n : ℕ} : ∑ k in range (n+1), k * choose (2*n) k
      + ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k - (n+(1:ℕ)) * choose (2*n) n
      = 2*(n:ℝ)*2^(2*n-1) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n := by
  rw [←two_mul, sum_range_choose_mul_eq, sum_range_choose_mul_half_eq]
  congr 1
  rw [cast_mul, ←mul_assoc, ←add_assoc]
  congr 3
  rw [cast_pow]
  congr 1
  congr 2
  rw [cast_one]
