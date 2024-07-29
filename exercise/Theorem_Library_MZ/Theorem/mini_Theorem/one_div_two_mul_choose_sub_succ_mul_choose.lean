import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem one_div_two_mul_choose_sub_succ_mul_choose (n : ℕ) (h : 1 ≤ n) : ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n
                                      = -(2*n+1) * choose (2*n-1) n := by
  have h41 : (((1/2) : ℝ)- (n + 1)) = - ((2*n+1) / 2) :=
    calc
      (((1/2) : ℝ)- (n + 1)) = - (n + 1/2) := by
        {
          rw [add_comm, ←sub_sub]
          norm_num
          congr 1
        }
      _ = - ((2*n+1) / 2) := by
        {
          congr 1
          rw [_root_.add_div, mul_comm]
          norm_num
        }
  have h42: 2*n = 2*n-1+1 := by
    have : 1 ≤ 2*n := by rw [two_mul]; linarith
    rw [Nat.sub_add_cancel this]
  have h43 : n = n-1+1 := by rw [Nat.sub_add_cancel h]
  have h44 : n * (n-1)! = n ! := by
    rw [h43,Nat.factorial_succ (n-1)]
    congr 1
  have h45 : n-1 = 2*n-1-n := by
    rw [two_mul, Nat.add_sub_assoc h, add_sub_self_left n (n - 1)]
  rw [←sub_mul, h41]
  rw [←neg_one_mul, ←neg_one_mul ((2*n+1) : ℝ), mul_assoc, mul_assoc]
  congr 1
  rw [choose_eq_factorial_div_factorial, cast_div, ←mul_div_assoc]
  rw [h42, Nat.factorial_succ (2*n-1), ←h42]
  norm_num
  rw [two_mul (n:ℕ)]
  norm_num
  rw [←two_mul (n:ℕ), h43, Nat.factorial_succ (n-1), ←h43]
  rw [div_mul, mul_assoc, ←div_div 2, div_self two_ne_zero, ←div_mul, div_one]
  rw [←mul_div, ←div_div, mul_comm (n:ℝ), cast_mul, ←mul_div, ←div_div (n:ℝ), div_self]
  rw [mul_one_div, div_div, ←cast_mul]
  rw [h44, choose_eq_factorial_div_factorial, cast_div, cast_mul]
  congr 2
  rw [mul_comm, h45] -- 第一个目标证明完成
  rw [←h45, two_mul, Nat.add_sub_assoc h]
  exact factorial_mul_factorial_dvd_factorial_add n (n - 1)
  rw [←h45, cast_ne_zero]
  exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero (n-1))
  linarith
  rw [cast_ne_zero]
  linarith
  rw [two_mul, Nat.add_sub_cancel]
  exact factorial_mul_factorial_dvd_factorial_add n n
  rw [two_mul, Nat.add_sub_cancel, cast_ne_zero]
  exact mul_ne_zero (factorial_ne_zero n) (factorial_ne_zero n)
  linarith
