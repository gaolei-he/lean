import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem factorial_mul_div_simp {n : ℕ} (h : 1 ≤ n) : ((n * (n * ((2:ℕ)*n-1)! / (n ! * (n * (n-1) !)))):ℝ)
                  = n * (((2:ℕ)*n-1)! / (n ! * (n-1) !)) := by
  congr 1
  rw [mul_comm, mul_div_assoc]
  rw [←cast_mul, ←cast_mul, mul_comm (n !) _, cast_mul]
  rw [div_mul_eq_div_div,cast_mul,div_mul_eq_div_div]
  rw [div_self, ←div_mul_eq_div_div, mul_one_div, mul_comm ((n-1)! : ℝ) _]
  rw [cast_ne_zero]
  linarith
