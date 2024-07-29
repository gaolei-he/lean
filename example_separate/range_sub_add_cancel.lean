import Theorem.example_separate.add_div_two
import Lean4Repl


open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem range_sub_add_cancel(h : 0 < n):  ∑ l in range (n-1+1),Nat.choose (n - 1) l = ∑ l in range n,Nat.choose (n - 1) l:= by lean_repl sorry
  refine' sum_congr _ fun y _ => rfl
  rw[Nat.sub_add_cancel]
  linarith
