import Lean4Repl
import Mathlib.Data.Real.Basic
import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem Ico_div : 1 / (2 * m + 1) * ∑ k in Ico 1 (2 * m + 1), k * (-1 : ℝ ) ^ k / choose (2 * m) (k-1) = 1 / (2 * m + 1) * ∑ l in Ico 0 (2 * m), (l+1) * (-1 : ℝ ) ^ (l+1) / choose (2 * m) l := by lean_repl sorry
  rw[sum_Ico_eq_sum_range]
  simp
  rw[range_eq_Ico]
  apply Or.inl
  refine' sum_congr rfl fun y _ => _
  rw[add_comm]
  congr 2
  rw[add_comm]
