import Mathlib.Data.Nat.Choose.Sum

open Nat
open Finset
open BigOperators

theorem Idt_66 {n : ℕ} : ∑ k in range (n+1), ((choose n k * 2^(n-k) * (-1)^k) : ℤ) = 1 := by
  have h1 : (((-1):ℤ) + 2)^n = ∑ k in range (n+1), ((-1):ℤ)^k * 2^(n-k) * choose n k := by
    exact add_pow ((-1):ℤ) 2 n
  nth_rw 1 [←one_add_one_eq_two, ←Int.add_assoc] at h1
  simp at h1
  have h2 : ∑ k in range (n + 1), ((-1):ℤ) ^ k * 2 ^ (n - k) * ↑(Nat.choose n k)
        = ∑ k in range (n + 1), ↑(Nat.choose n k) * 2 ^ (n - k) * ((-1):ℤ) ^ k := by
    refine' sum_congr rfl fun k hk => _
    rw [mul_rotate, Int.mul_comm (2 ^ (n - k)) ((Nat.choose n k):ℤ)]
  rw [←h2, ←h1]
