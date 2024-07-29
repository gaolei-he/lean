import Lean4Repl
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem sum_range_eq_Ico_succ_bot {n : ℕ} : ((∑ k in range (n+1), k * choose (2*n+1) k) : ℝ)
            = ∑ k in Ico 1 (n + 1), k * choose (2*n+1) k := by lean_repl sorry
  have h_gt_zero : 0 < n + 1 := by linarith
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot h_gt_zero]
  simp
