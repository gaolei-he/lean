import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem succ_sub (n : ℕ) (h : 1 < n): succ (n-1) = n := by
  have h1 : 1 ≤ 1 := by linarith
  have h2 : 1 ≤ n := by linarith
  rw [succ_eq_add_one]
  rw [←tsub_tsub_assoc h2 h1]
  simp
