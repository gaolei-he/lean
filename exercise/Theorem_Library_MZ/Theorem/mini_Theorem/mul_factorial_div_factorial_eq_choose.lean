import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem mul_factorial_div_factorial_eq_choose {n : ℕ} (h : 1 ≤ n) : ((n * (((2:ℕ)*n-1)! / (n ! * (n-1) !))) : ℝ)
                 = n * choose (2*n-1) n := by
  congr 1
  have : n-1 = 2*n-1-n := by
    rw [two_mul, Nat.add_sub_assoc h, add_sub_self_left n (n - 1)]
  rw [this]
  rw [choose_eq_factorial_div_factorial, cast_div, cast_mul]
  all_goals (try rw [←this])
  rw [two_mul, Nat.add_sub_assoc h]
  exact factorial_mul_factorial_dvd_factorial_add n (n-1)
  rw [cast_ne_zero]
  exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero (n-1))
  rw [two_mul]
  have h1 : n - 1 + n = n + n - 1 := by exact tsub_add_eq_add_tsub h
  rw [←h1]
  exact Nat.le_add_left n (n - 1)
