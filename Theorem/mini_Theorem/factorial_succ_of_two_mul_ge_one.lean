import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators



theorem factorial_succ_of_two_mul_ge_one {n : ℕ} (h : 1 ≤ n) : n * ((1/2):ℝ) * ((2*n)! / ((n)! * (2*n -n)!))
                = n * ((1/2):ℝ) * (((2:ℕ)*n-1+1)*((2:ℕ)*n-1)! / (n ! * n !)) := by
  congr 1
  have : 2*n = 2*n-1+1 := by
    have : 1 ≤ 2*n := by rw [two_mul];linarith
    rw [Nat.sub_add_cancel this]
  rw [this]
  rw [Nat.factorial_succ (2*n-1)]
  rw [←this, cast_mul, ←cast_mul 2 n]
  rw [sub_add_cancel]
  congr 3
  rw [two_mul, Nat.add_sub_cancel]
