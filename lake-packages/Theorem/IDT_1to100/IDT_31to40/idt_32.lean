import Mathlib.Data.Nat.Choose.Sum

open Int
open Nat
@[simp]
def rise (x : ℤ) : ℕ → ℤ
| 0 => 1
| k + 1 => x * rise (x + 1) k

@[simp]
def fall (x : ℤ) : ℕ → ℤ
| 0 => 1
| k + 1 => x * fall (x - 1) k


theorem idt_32 (n : ℕ) : (k : ℕ) → rise (ofNat n) k = (- 1) ^ k * fall (negOfNat n) k
| 0 => by simp
| k' + 1 => by
    simp
    have h1 (n : ℤ) (k : ℕ) : n ^ (k + 1) = n ^ k * n := rfl
    rw [h1, Eq.symm (mul_assoc _ _ _), mul_assoc (((-1:ℤ)) ^ k') (-1) _]
    have h2: -1 * negOfNat n = ofNat n := by
      cases n
      simp [negOfNat]
      simp [negOfNat]
      rfl
    rw [h2, mul_comm ((-1:ℤ) ^ k'), mul_assoc]
    let h (n : ℕ) : ofNat (n + 1) = ofNat n + 1 := rfl
    let h' (n : ℕ) : negOfNat (n + 1) = negOfNat n - 1 := by
      cases n
      simp[negOfNat]
      simp[Neg.neg, Int.neg, negOfNat]
      -- rfl
    have := idt_32 (n + 1) k'
    rw [h, h'] at this
    rw [this.symm]
    rfl
