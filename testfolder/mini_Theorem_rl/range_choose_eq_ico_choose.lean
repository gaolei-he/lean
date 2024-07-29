import Theorem.example_separate.add_div_two
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem range_choose_eq_ico_choose(h : 2 ≤ n )  :  ∑ l in range (n-2+1), Nat.choose (n - 2) l = ∑ s in Ico 0 (n-1), choose (n-2) s:= by lean_repl sorry
      refine' sum_congr _ fun y _ => rfl
      rw[← Nat.sub_add_comm]
      simp
      linarith
