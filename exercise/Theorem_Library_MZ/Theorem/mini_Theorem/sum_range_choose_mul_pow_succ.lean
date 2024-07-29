import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_range_choose_mul_pow_succ (x : ℕ) (h : 0 < x): 1 / (n + 1) * ∑ k in range (n + 1), Nat.choose (n + 1) (k + 1) * ((x ^ k) : ℝ)
            = 1 / ((n + 1) * x) * ∑ k in range (n + 1), Nat.choose (n + 1) (k + 1) * ((x ^ (k+1)) : ℝ) := by
  rw [mul_sum, mul_sum]
  rw [div_mul_eq_div_mul_one_div]
  refine' sum_congr rfl fun y hy => _
  rw [pow_add,mul_assoc]
  congr 1
  rw [←mul_assoc]
  rw [mul_comm  (1/(x:ℝ))  ((Nat.choose (n + 1) (y + 1)) : ℝ)]
  rw [mul_assoc]
  congr 1
  rw [div_mul,mul_comm]
  simp
  rw [mul_div_right_comm, div_self]
  simp
  have : x ≠ 0 := by exact Iff.mp Nat.pos_iff_ne_zero h
  exact Iff.mpr cast_ne_zero this
