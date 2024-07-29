import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sub_one_eq_two_mul_sub_one_sub {n : ℕ} (h : 1 ≤ n) : n-1 = 2*n-1-n := by
    rw [two_mul, Nat.add_sub_assoc h, add_sub_self_left n (n - 1)]
