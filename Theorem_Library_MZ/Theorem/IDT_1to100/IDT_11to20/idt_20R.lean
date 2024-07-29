import Mathlib
import Mathlib.Data.Nat.Choose.Sum
import Theorem.IDT_1to100.IDT_11to20.idt_20Z

open Nat
open Finset
open BigOperators



theorem Idt20' {n k : ℕ} {h1 : n >=1 } : ∑ k in range (m +1), (Nat.choose n k) * (-1:ℝ)^k = (-1:ℝ)^m * Nat.choose (n -1) m :=by
  have l₁: ∑ k in range (m +1), (Nat.choose n k) * (-1:ℤ)^k = (-1:ℤ)^m * Nat.choose (n -1) m →
  ∑ k in range (m +1), (Nat.choose n k) * (-1:ℝ)^k = (-1:ℝ)^m * Nat.choose (n -1) m :=by
    ring_nf
    intro h
    have h2: ∑ x in range (1 + m), ↑(Nat.choose n x) * (-1:ℤ) ^ x = ∑ x in range (1 + m), ↑(Nat.choose n x) * (-1:ℝ) ^ x :=by
      simp [←cast_mul]
    rw [Int.cast] at h2
    symm at h2
    rw [h2]
    rw [h]
    simp
  rw [l₁]
  rw [Idt20]
  exact n
  exact h1
