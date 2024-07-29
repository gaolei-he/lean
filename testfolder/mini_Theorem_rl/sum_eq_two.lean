import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem sum_eq_two (n : Nat):
  2 ^ ( 2 * n ) = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by lean_repl sorry
   rw [sum_range_add_sum_Ico _ ]
   rw [← sum_range_choose]
   linarith
