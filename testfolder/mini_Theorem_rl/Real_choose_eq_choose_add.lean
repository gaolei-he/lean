import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Real.Basic
import Lean4Repl

open Nat

set_option maxHeartbeats 999999999999999999999999

theorem Real_choose_eq_choose_add(h1:1 ≤ n)(h2:1 ≤ k) : (choose n k : ℝ) = (choose (n-1) k : ℝ)  + (choose (n-1) (k-1): ℝ) := by lean_repl sorry
  rw[← Nat.sub_add_cancel h1, ← Nat.sub_add_cancel h2]
  simp
  rw[choose_succ_succ]
  rw[add_comm]
  simp
