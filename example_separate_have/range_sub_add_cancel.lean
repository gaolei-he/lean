import Theorem.example_separate.add_div_two


open Finset

open BigOperators

theorem range_sub_add_cancel(h : 0 < n):  ∑ l in range (n-1+1),Nat.choose (n - 1) l = ∑ l in range n,Nat.choose (n - 1) l:= by
  have h': 1 ≤ n := by linarith
  refine' sum_congr _ fun y _ => rfl
  have nn: n - 1 + 1 = n := by
    exact Nat.sub_add_cancel h'
  rw[nn]
