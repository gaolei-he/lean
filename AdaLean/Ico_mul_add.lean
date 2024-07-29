import Mathlib.Data.Nat.Choose.Sum
import AdaLean.range_mul_add

open Nat

open Finset

open BigOperators


theorem Ico_mul_add : ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l = ∑ l in Ico 0 n, l * Nat.choose (n - 1) l + ∑ l in Ico 0 n,  Nat.choose (n - 1) l := by
  rw[← range_eq_Ico]
  rw[range_mul_add]
  rw[sum_add_distrib]
  simp
