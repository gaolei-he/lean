import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem cast_mul_mul_choose_eq_factorial_div_factorial {n : ℕ} : n * (((1/2):ℝ) * choose (2*n) n)
                  = n * ((1/2):ℝ) * ((2*n)! / ((n)! * (2*n -n)!)) := by
  rw [choose_eq_factorial_div_factorial]
  rw [←mul_assoc,←cast_mul, ←cast_div]
  rw [two_mul, Nat.add_sub_cancel]
  exact factorial_mul_factorial_dvd_factorial_add n n
  rw [two_mul, Nat.add_sub_cancel]
  rw [cast_ne_zero]
  exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero n)
  linarith
