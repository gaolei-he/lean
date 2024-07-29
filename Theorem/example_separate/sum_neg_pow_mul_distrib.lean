import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_neg_pow_mul_distrib: ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (((-1 : ℝ)^k * choose (n-1) k + (-1 : ℝ)^k * choose (n-1) (k-1)) : ℝ) * (m / (m+k)) := by
    refine' sum_congr rfl fun y _ => _
    rw[mul_add]


theorem sum_neg_pow_mul_distrib_from_1_to_1(n : ℕ)(m : ℝ)(y : ℕ)(x✝ : y ∈ Ico 1 n) :
   (-1 : ℝ) ^ y * (↑(Nat.choose (n - 1) y) + ↑(Nat.choose (n - 1) (y - 1))) * (m / (m + ↑y)) =
    ((-1 : ℝ) ^ y * ↑(Nat.choose (n - 1) y) + (-1 : ℝ) ^ y * ↑(Nat.choose (n - 1) (y - 1))) * (m / (m + ↑y)) := by
  rw[mul_add]

