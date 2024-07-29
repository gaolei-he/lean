import Mathlib.Data.Nat.Choose.Sum
import AdaLean.range_sub_add_cancel

open Nat

open Finset

open BigOperators

theorem ico_two_pow(h : 0 < n): ∑ l in Ico 0 n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  rw[← range_eq_Ico]
  rw[range_sub_add_cancel h]
