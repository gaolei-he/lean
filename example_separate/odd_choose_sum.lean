import Mathlib.Data.Real.Basic
import Theorem.example_separate.add_div_two
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem odd_choose_sum(hnm: n = 2 * m + 1): ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = ∑ k in Ico 1 (2 * m + 1), (-1 : ℝ ) ^ k / choose (2 * m + 1) k := by lean_repl sorry
  rw[hnm]
  rw[sum_range_succ]
  rw[range_eq_Ico]
  rw[sum_eq_sum_Ico_succ_bot]
  norm_num
  linarith
