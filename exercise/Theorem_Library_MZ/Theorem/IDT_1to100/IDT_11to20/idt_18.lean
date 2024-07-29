import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith

open Nat

open Finset

open BigOperators

theorem Identity_18 (n : ℕ): (x + 1) ^ n = ∑ k in range (n + 1), choose n k * x ^ k := by
  have h1: (x + 1) ^ n = ∑ m in range (n + 1), x ^ m * 1 ^ (n - m) * choose n m := by
    exact add_pow x 1 n
  have h2: (x + 1) ^ n = ∑ k in range (n + 1), x ^ k * 1 ^ (n - k) * choose n k := by
    exact h1
  rw[h2]
  have h3 (n : ℕ):
  ∑ k in range (n + 1), x ^ k * 1 ^ (n - k) * choose n k = ∑ k in range (n + 1),choose n k * x ^ k * 1 ^ (n - k) := by
    refine' sum_congr rfl fun y hy => _
    exact (mul_rotate (Nat.choose n y) (x ^ y) (1 ^ (n - y))).symm
  -- have h4 (k : ℕ): 1 ^ (n - k) = 1:= by
  --   exact Nat.one_pow (n - k)
  rw[h3]
  have h5 (n : ℕ)(k: ℕ ): choose n k * x ^ k * 1 ^ (n - k) = choose n k * x ^ k * 1 := by
    have d1(k : ℕ): 1 ^ (n - k) = 1:= by
      exact Nat.one_pow (n - k)
    exact congrArg (HMul.hMul (Nat.choose n k * x ^ k)) (d1 k)
  have h6 (n : ℕ):
  ∑ k in range (n + 1),choose n k * x ^ k * 1 ^ (n - k) = ∑ k in range (n + 1),choose n k * x ^ k * 1 := by
    refine' sum_congr rfl fun y hy => _
    rw[h5]
  rw[h6]
  have h7 (n : ℕ):
  ∑ k in range (n + 1), choose n k * x ^ k * 1 = ∑ k in range (n + 1), choose n k * x ^ k:= by
    have d2(k : ℕ): choose n k * x ^ k * 1 = choose n k * x ^ k := by
      exact Nat.mul_one (Nat.choose n k * x ^ k)
    refine' sum_congr rfl fun y hy => _
    exact d2 y
  rw[h7]
