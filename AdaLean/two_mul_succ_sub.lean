import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators


theorem two_mul_succ_sub (hn: n ≤ 2 * n): 2 * n + 1 - n = n + 1 := by
  rw[add_comm]
  rw[Nat.add_sub_assoc hn]
  rw[add_comm]
  rw[Nat.two_mul]
  simp
