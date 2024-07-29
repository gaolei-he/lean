import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators


theorem pow_add_one_sub_one {n : ℕ} (h : n ≠ 0) : 2^n = 2^(n - 1 + 1) := by
  have hone_le_one : 1 ≤ 1 := by linarith
  have hone_le_n : 1 ≤ n := by exact Iff.mpr one_le_iff_ne_zero h
  rw [←tsub_tsub_assoc hone_le_n hone_le_one]
  simp
