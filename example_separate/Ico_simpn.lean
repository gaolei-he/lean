import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Lean4Repl


open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem Ico_simpn (hn : 1 ≤ n): ∑ k in Ico 1 (n+1), (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ)) =
   ∑ k in Ico 1 n, (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ) ) := by lean_repl sorry
    rw [sum_Ico_succ_top hn]
    simp
