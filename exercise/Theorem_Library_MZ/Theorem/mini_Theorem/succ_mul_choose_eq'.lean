import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem succ_mul_choose_eq' {n k : ℕ} (h0 : 1 < n) (h1 : 1 ≤ k): n * choose (n-1) (k-1) = k * choose n k := by
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by linarith
  have h2 : succ (n-1) = n := by
    rw [succ_eq_add_one]
    rw [←tsub_tsub_assoc hone_le_n hone_le_one]
    simp
  have h3 : succ (k-1) = k := by
    rw [succ_eq_add_one]
    rw [←tsub_tsub_assoc h1 hone_le_one]
    simp
  rw [←h2, ←h3]
  simp
  rw [succ_mul_choose_eq]
  rw [mul_comm]
