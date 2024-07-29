import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Theorem.mini_Theorem.sub_one_add_one
import Lean4Repl

open Nat

open Finset

open BigOperators

theorem factorial_succ_ge_one {n : ℕ} (h : 1 ≤ n) : n * (n-1)! = n ! := by lean_repl sorry
    rw [sub_one_add_one h, Nat.factorial_succ (n-1)]
    congr 1
