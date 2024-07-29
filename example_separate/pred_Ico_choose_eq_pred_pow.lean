import Theorem.example_separate.add_div_two
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem pred_Ico_choose_eq_pred_pow(hn : 2 ≤ n ) :  (n - 1) * ∑ s in Ico 0 (n-1), choose (n-2) s + 2 ^ ( n - 1 ) = (n - 1) * 2 ^ (n-2)  + 2 ^ ( n - 1 ) := by lean_repl sorry
  rw[← range_eq_Ico]
  rw [← sum_range_choose (n - 2)]
  congr 1
  simp
  rw[or_iff_left]
  refine' sum_congr _ fun y _ => rfl
  congr 1
  rw[← Nat.sub_add_comm]
  simp
  linarith
  simp
  linarith
