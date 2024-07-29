import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem half_sub_eq_neg_two_mul_add_div {n : ℕ}: (((1/2) : ℝ)- (n + 1)) = - ((2*n+1) / 2) :=
  calc
    (((1/2) : ℝ)- (n + 1)) = - (n + 1/2) := by
      {
        rw [add_comm, ←sub_sub]
        norm_num
        congr 1
      }
    _ = - ((2*n+1) / 2) := by
      {
        congr 1
        rw [_root_.add_div, mul_comm]
        norm_num
      }
