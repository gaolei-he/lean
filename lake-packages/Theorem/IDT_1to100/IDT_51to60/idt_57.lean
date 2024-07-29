import Mathlib.Data.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Basic

-- Mathlib/Data/Nat/Choose/Vandermonde.lean

#align_import linear_algebra.vandermonde from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"


open BigOperators
open Polynomial Finset Finset.Nat


theorem idt57_vandermonde (m n k : ℕ) :
    (m + n).choose k = ∑ ij : ℕ × ℕ in antidiagonal k, m.choose ij.1 * n.choose ij.2 := by
  calc
    (m + n).choose k = ((X + 1) ^ (m + n)).coeff k := by rw [coeff_X_add_one_pow, Nat.cast_id]
    _ = ((X + 1) ^ m * (X + 1) ^ n).coeff k := by rw [pow_add]
    _ = ∑ ij : ℕ × ℕ in antidiagonal k, m.choose ij.1 * n.choose ij.2 := by
      rw [coeff_mul, Finset.sum_congr rfl]
      simp only [coeff_X_add_one_pow, Nat.cast_id, eq_self_iff_true, imp_true_iff]
