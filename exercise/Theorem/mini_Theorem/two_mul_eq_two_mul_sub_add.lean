import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem two_mul_eq_two_mul_sub_add {n : ℕ} (h : 1 ≤ n) : 2*n = 2*n-1+1 := by
  have : 1 ≤ 2*n := by rw [two_mul]; linarith
  rw [Nat.sub_add_cancel this]
