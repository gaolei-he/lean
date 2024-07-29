import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators


theorem add_two_subY(n y : ℕ): n - (2 * n - y) =(-1:ℝ)*(n - y) := by
 simp
 rw[two_mul]
 rw[sub_eq_neg_add]
 rw[neg_sub]
 rw[sub_eq_neg_add]
 rw[neg_add]
 rw[sub_eq_neg_add]
 rw[add_assoc]
 rw[add_comm]
 rw[← add_assoc]
 rw[add_comm]
 congr 1
 rw[add_assoc]
 simp
