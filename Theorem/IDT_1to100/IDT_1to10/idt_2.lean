import Mathlib.Data.Nat.Choose.Sum


#align_import data.nat.choose.basic from "leanprover-community/mathlib"@"2f3994e1b117b1e1da49bcfb67334f33460c3ce4"

open Nat



theorem idt2 {n k : ℕ} (hk : k ≤ n) :
    choose n k = n ! / (k ! * (n - k)!) := by
  rw [← choose_mul_factorial_mul_factorial hk, mul_assoc]
  exact (mul_div_left _ (mul_pos (factorial_pos _) (factorial_pos _))).symm
