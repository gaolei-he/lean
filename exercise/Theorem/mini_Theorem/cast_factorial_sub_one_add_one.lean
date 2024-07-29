import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem cast_factorial_sub_one_add_one {n : ℕ} : n * ((1/2):ℝ) * (((2:ℕ)*n-1+1)*((2:ℕ)*n-1)! / (n ! * n !))
                = n * (((1/2):ℝ) * ((2:ℕ)*n)*((2:ℕ)*n-1)! / (n ! * n !)) := by
  rw [sub_add_cancel, mul_assoc]
  congr 1
  rw [←cast_mul,←cast_mul,←cast_mul,←mul_div_assoc]
  congr 1
  rw [cast_mul,←mul_assoc]
