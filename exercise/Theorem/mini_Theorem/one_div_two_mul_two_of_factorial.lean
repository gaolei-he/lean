import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem one_div_two_mul_two_of_factorial {n : ℕ} : n * (((1/2):ℝ) * ((2:ℕ)*n)*((2:ℕ)*n-1)! / (n ! * n !))
                  = n * (n * ((2:ℕ)*n-1)! / (n ! * n !)) := by simp
