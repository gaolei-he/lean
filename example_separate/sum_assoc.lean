import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem sum_assoc : ∑ k in Ico 1 (2 * m), (-1 : ℝ) * (-1 : ℝ) ^ (k - 1) / Nat.choose (2 * m) k = ∑ k in Ico 1 (2 * m), (-1 : ℝ) * ((-1 : ℝ) ^ (k - 1) / Nat.choose (2 * m) k) := by lean_repl sorry
  refine' sum_congr rfl fun y _ => _
  rw[← mul_div]
