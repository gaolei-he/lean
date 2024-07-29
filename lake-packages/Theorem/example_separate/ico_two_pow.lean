import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem ico_two_pow(h : 0 < n): ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have h': 1 ≤ n := by linarith
  rw[← range_eq_Ico]
  have nn: n - 1 + 1 = n := by
      exact Nat.sub_add_cancel h'
  have range_sub_add_cancel :  ∑ l in range (n-1+1),Nat.choose (n - 1) l = ∑ l in range n,Nat.choose (n - 1) l:= by
    refine' sum_congr _ fun y _ => rfl
    rw[nn]
  rw[sum_range_choose] at range_sub_add_cancel
  rw[range_sub_add_cancel]


theorem ico_two_pow_from_0_to_0(n : ℕ)(h : 0 < n)(gol:  ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have h': 1 ≤ n := by linarith
  apply gol

theorem ico_two_pow_from_0_to_1(n : ℕ)(h : 0 < n)(gol:  ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have h': 1 ≤ n := by linarith
  rw[← range_eq_Ico]
  apply gol

theorem ico_two_pow_from_0_to_2(n : ℕ)(h : 0 < n)(gol:  ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have h': 1 ≤ n := by linarith
  rw[← range_eq_Ico]
  have nn: n - 1 + 1 = n := by
      exact Nat.sub_add_cancel h'
  apply gol

theorem ico_two_pow_from_1_to_1(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(gol:  ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  rw[← range_eq_Ico]
  apply gol

theorem ico_two_pow_from_1_to_2(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(gol:  ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  rw[← range_eq_Ico]
  have nn: n - 1 + 1 = n := by
      exact Nat.sub_add_cancel h'
  apply gol

theorem ico_two_pow_from_2_to_2(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(gol:  ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have nn: n - 1 + 1 = n := by
      exact Nat.sub_add_cancel h'
  apply gol

theorem ico_two_pow_from_4_to_4(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(nn : n - 1 + 1 = n)(range_sub_add_cancel : ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l = ∑ l in range n, Nat.choose (n - 1) l)(gol:  ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  rw[sum_range_choose] at range_sub_add_cancel
  apply gol

theorem ico_two_pow_from_4_to_5(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(nn : n - 1 + 1 = n)(range_sub_add_cancel : ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l = ∑ l in range n, Nat.choose (n - 1) l) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  rw[sum_range_choose] at range_sub_add_cancel
  rw[range_sub_add_cancel]

theorem ico_two_pow_from_5_to_5(n : ℕ)(h : 0 < n)(h' : 1 ≤ n)(nn : n - 1 + 1 = n)(range_sub_add_cancel : 2 ^ (n - 1) = ∑ l in range n, Nat.choose (n - 1) l) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  rw[range_sub_add_cancel]

