import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem two_mul_sub_one_add_one_sub {n : ℕ} (h : 0 < n) : 2 * n - 1 + 1 - n = n := by
  have : 1 ≤ 2 * n := by linarith
  rw [Nat.sub_add_cancel this]
  rw [two_mul]
  simp
