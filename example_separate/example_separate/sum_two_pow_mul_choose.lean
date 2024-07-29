import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem sum_two_pow_mul_choose {n : ℕ} : ∑ k in range (n+1), 2^k * choose n k = 3^n := by
  have : ∑ m in range (n + 1), 2 ^ m * 1 ^ (n - m) * ↑(Nat.choose n m) = (2 + 1) ^ n :=
    (add_pow _ _ _).symm
  simp at this
  assumption
