import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem ico_two_pow(h : 0 < n): ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have h': 1 ≤ n := by linarith
  rw[← range_eq_Ico]
  have range_sub_add_cancel :  ∑ l in range (n-1+1),Nat.choose (n - 1) l = ∑ l in range n,Nat.choose (n - 1) l:= by
    refine' sum_congr _ fun y _ => rfl
    have nn: n - 1 + 1 = n := by
      exact Nat.sub_add_cancel h'
    rw[nn]
  rw[sum_range_choose] at range_sub_add_cancel
  rw[range_sub_add_cancel]
