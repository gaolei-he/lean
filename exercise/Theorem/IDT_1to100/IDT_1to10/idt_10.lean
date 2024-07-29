import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat Finset BigOperators

theorem idt_10 {n k: ℕ} (h0 : 2 ≤ k) (h1 : k ≤ n): ((k * (k-1) * (choose n k)):ℝ)
                                                  = ((n * (n-1) * (choose (n-2) (k-2))):ℝ) := by
  have h21 (k : ℕ) (h0 : 2 ≤ k) : k-2+1 = k-1 := by
    rw [←one_add_one_eq_two, ←Nat.sub_sub, Nat.sub_add_cancel]
    exact le_sub_one_of_lt h0
  have h22 (k : ℕ) (h0 : 2 ≤ k) : succ (k-2) = k-1 := by
    exact h21 k h0
  have h23 (k : ℕ) (h0 : 2 ≤ k) : k-1+1 = k := by
    rw [Nat.sub_add_cancel]
    linarith
  have h2 (k : ℕ) (h0 : 2 ≤ k) : k*(k-1)*(k-2)! = k ! := by
    rw [←h21 k h0, mul_assoc]
    rw [←Nat.factorial_succ (k-2), h22 k h0]
    nth_rw 1 [←h23 k h0]
    rw [←Nat.factorial_succ (k-1)]
    rw [←add_one, h23 k h0]
  have h3 : ((k*(k-1)):ℝ) ≠ 0 := by
    have h31 : k-1 ≠ 0 := by exact sub_ne_zero_of_lt h0
    have h32 : k ≠ 0 := by exact not_eq_zero_of_lt h0
    rw [←cast_one, ←cast_sub, ←cast_mul, cast_ne_zero]
    exact mul_ne_zero h32 h31
    linarith
  have h4 : n-2-(k-2) = n-k := by
    exact tsub_tsub_tsub_cancel_right h0
  have h5 : n - 2 = k - 2 + (n - k) := by
    rw [←Nat.sub_add_comm, ←Nat.add_sub_assoc h1]
    norm_num
    linarith
  have h6 : k + (n - k) = n := by exact add_sub_of_le h1
  rw [choose_eq_factorial_div_factorial,cast_div, mul_div, mul_comm,←h2 k]
  norm_num
  rw [cast_sub, cast_one, ←div_div (_ * _), ←div_div (_ * _), mul_div_assoc, div_self h3]
  norm_num
  rw [div_div,choose_eq_factorial_div_factorial, cast_div, mul_div,
      ←cast_one, ←cast_sub,←cast_mul,←cast_mul,←cast_mul, h2 n, h4]
  all_goals (try linarith)
  rw [h4,h5]
  exact factorial_mul_factorial_dvd_factorial_add (k-2) (n-k)
  rw [cast_ne_zero, h4]
  exact mul_ne_zero (factorial_ne_zero (k-2)) (factorial_ne_zero (n-k))
  nth_rw 2 [←h6]
  exact factorial_mul_factorial_dvd_factorial_add k (n-k)
  rw [cast_ne_zero]
  exact mul_ne_zero (factorial_ne_zero k) (factorial_ne_zero (n-k))
