import Theorem.example_separate.add_div_two
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem ico_succ: ∑ s in Ico 0 (n-1), choose (n-2) s = ∑ l in Ico 1 n, choose (n-2) (l-1) := by lean_repl sorry
    rw[sum_Ico_eq_sum_range]
    simp
    rw[sum_Ico_eq_sum_range]
    refine' sum_congr rfl fun y _ => _
    simp
