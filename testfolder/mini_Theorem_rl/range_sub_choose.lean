import Theorem.example_separate.Ico_choose_range_choose
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by lean_repl sorry
  rw[Ico_choose_range_choose]
