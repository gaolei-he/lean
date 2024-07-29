import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem pow_sub_one_succ {n : ℕ} : 2^(n - 1 + 1) = 2 * 2^(n-1) := by
  rw [add_one]
  rw [_root_.pow_succ 2 (n-1)]
