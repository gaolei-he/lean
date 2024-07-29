import Mathlib.LinearAlgebra.Vandermonde

#align_import linear_algebra.vandermonde from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"



variable {R : Type*} [CommRing R]



open BigOperators Matrix

namespace Matrix


theorem idt57_vandermonde {n : ℕ} (v w : Fin n → R) (i j) :
    (vandermonde v * (vandermonde w)ᵀ) i j = ∑ k : Fin n, (v i * w j) ^ (k : ℕ) := by
  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_pow]




end Matrix
