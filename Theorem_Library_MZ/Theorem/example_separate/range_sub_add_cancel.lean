import Theorem.example_separate.add_div_two


open Finset

open BigOperators

theorem range_sub_add_cancel(h : 0 < n):  ∑ l in range (n-1+1),Nat.choose (n - 1) l = ∑ l in range n,Nat.choose (n - 1) l:= by
  have h': 1 ≤ n := by linarith
  refine' sum_congr _ fun y _ => rfl
  have nn: n - 1 + 1 = n := by
    exact Nat.sub_add_cancel h'
  rw[nn]


theorem range_sub_add_cancel_from_0_to_0(n : ℕ)(h : 0 < n)(gol:  ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l = ∑ l in range n, Nat.choose (n - 1) l) :
   ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l = ∑ l in range n, Nat.choose (n - 1) l := by
  have h': 1 ≤ n := by linarith
  apply gol

theorem range_sub_add_cancel_from_2_to_2(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(gol:  range (n - 1 + 1) = range n) :
   range (n - 1 + 1) = range n := by
  have nn: n - 1 + 1 = n := by
    exact Nat.sub_add_cancel h'
  apply gol

theorem range_sub_add_cancel_from_2_to_3(n : ℕ)(h : 0 < n)(h' : 1 ≤ n) :
   range (n - 1 + 1) = range n := by
  have nn: n - 1 + 1 = n := by
    exact Nat.sub_add_cancel h'
  rw[nn]

theorem range_sub_add_cancel_from_3_to_3(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(nn : n - 1 + 1 = n) :
   range (n - 1 + 1) = range n := by
  rw[nn]

