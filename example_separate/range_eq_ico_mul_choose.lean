import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by lean_repl sorry
  rw[range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot]
  linarith
  simp
