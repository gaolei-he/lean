import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem two_mul_sub_one_add_one_sub_zero {n : ℕ} (h : 0 < n) : 2 * n - 1 + 1 - 0 = 2 * n := by
  simp
  have : 1 ≤ 2 * n := by linarith
  rw [Nat.sub_add_cancel this]
