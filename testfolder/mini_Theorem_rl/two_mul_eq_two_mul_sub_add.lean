import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl

open Nat

open Finset

open BigOperators

theorem two_mul_eq_two_mul_sub_add {n : ℕ} (h : 1 ≤ n) : 2*n = 2*n-1+1 := by lean_repl sorry
  have : 1 ≤ 2*n := by rw [two_mul]; linarith
  rw [Nat.sub_add_cancel this]
