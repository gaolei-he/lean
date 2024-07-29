import Theorem.example_separate.choose_mul_eq_mul_sub

open Nat

theorem pow_mul_choose {n k : ℕ}(hkn : k ≤ n)(hsk : 1 ≤ k) :
  k ^ 2 * choose n k = n * k * choose (n-1) (k-1)  := by
    have mul_same : choose n k * k * k  = n * k * choose (n - 1) (k - 1)  := by   -- 两边同时*k
      rw [choose_mul_eq_mul_sub (hkn) (hsk)]  -- n * Nat.choose (n - 1) (k - 1) * k = n * Nat.choose (n - 1) (k - 1) * k
      rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]  --choose n k * k * k  = n * k * choose (n - 1) (k - 1)
    have choose_mul_pow_eq_mul : choose n k * (k ^ 2)  = n * k * choose (n - 1) (k - 1)  := by
      rw[Nat.mul_assoc] at mul_same
      rw[pow_two, mul_same]
    rw[mul_comm, choose_mul_pow_eq_mul]
