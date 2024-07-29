import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Parity

open Nat

open Finset

open BigOperators

theorem ite_add_eq_sub_neg {n : ℕ} : ∑ k in range (n+1), (if k % 2 = 1 then ((choose n k) : ℤ) + ((choose n k) : ℤ) else ((choose n k) : ℤ) - ((choose n k) : ℤ))
        = ∑ k in range (n+1), ((if k % 2 = 1 then choose n k - (-1)^k * choose n k else choose n k - (-1)^k * choose n k) : ℤ) := by
        refine' sum_congr rfl fun y fy => _
        split_ifs with h'
        . rw [←Nat.odd_iff] at h'
          rw [Odd.neg_one_pow h']
          rw [neg_one_mul]
          rw [sub_neg_eq_add]
        . rw [Nat.mod_two_ne_one, ←Nat.even_iff] at h'
          rw [Even.neg_one_pow h']
          simp
