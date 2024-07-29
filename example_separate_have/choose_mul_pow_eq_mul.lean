import Theorem.example_separate.choose_mul_eq_mul_sub

open Nat

theorem choose_mul_pow_eq_mul(hkn : k ≤ n)(hsk : 1 ≤ k): choose n k * (k ^ 2)  = n * k * choose (n - 1) (k - 1)  := by
  have mul_same : choose n k * k * k  = n * k * choose (n - 1) (k - 1)  := by
      rw [choose_mul_eq_mul_sub (hkn) (hsk)]
      rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]
  rw[Nat.mul_assoc] at mul_same
  rw[pow_two, mul_same]
