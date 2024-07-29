import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem le_two_mul_sub_one_add_one {n : ℕ} (h : 0 < n) : n ≤ 2 * n - 1 + 1 := by
  have : 1 ≤ 2 * n := by linarith
  rw [Nat.sub_add_cancel this]
  linarith
