import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic



open Nat

open Finset

open BigOperators

lemma neg_two_one_pow_add_n (n:ℕ) :
  ∑ m in range (n + 1), (-2:ℝ) ^ (m) *  (1) ^ (n -m) * ↑(Nat.choose n m) = (-1:ℝ)^n  :=by
    rw [←add_pow]
    ring
