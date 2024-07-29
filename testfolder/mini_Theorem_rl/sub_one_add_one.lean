import Lean4Repl
import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem sub_one_add_one {n : ℕ} (h : 1 ≤ n) : n = n-1+1 := by lean_repl sorry
rw [Nat.sub_add_cancel h]
