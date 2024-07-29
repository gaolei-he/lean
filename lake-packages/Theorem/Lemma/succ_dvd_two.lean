import Mathlib.Data.Nat.Choose.Sum

open Nat Finset BigOperators


theorem succ_dvd_two {n : ℕ} : 2 ∣ (n + 1) * n := by
  induction n
  . simp
  . rename_i n h₁
    rw [←add_one, add_mul, add_mul, mul_comm]
    simp
    rw [add_assoc, ←two_mul]
    have h₂ : 2 ∣ 2 * (n + 1) := by
      simp
    apply Nat.dvd_add h₁ h₂
