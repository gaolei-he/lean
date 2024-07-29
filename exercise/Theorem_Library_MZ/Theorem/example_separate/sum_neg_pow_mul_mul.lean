import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_neg_pow_mul_mul (t : ℕ → ℕ → ℕ → ℝ := fun m n k => (-1 : ℝ)^k * (choose n k : ℝ) * (m / (m+k))):
  ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (((-1 : ℝ)^k * choose (n-1) k * (m / (m+k)) + (-1 : ℝ)^k * choose (n-1) (k-1) * (m / (m+k))) : ℝ):= by
  have sum_neg_pow_mul_distrib: ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (((-1 : ℝ)^k * choose (n-1) k + (-1 : ℝ)^k * choose (n-1) (k-1)) : ℝ) * (m / (m+k)) := by
    refine' sum_congr rfl fun y _ => _
    rw[mul_add]
  rw[sum_neg_pow_mul_distrib]
  refine' sum_congr rfl fun y _ => _
  rw[add_mul]


theorem sum_neg_pow_mul_mul_from_1_to_1(n : ℕ)(m : ℝ)(t : optParam (ℕ → ℕ → ℕ → ℝ) fun m n k => (-1 : ℝ) ^ k * ↑(Nat.choose n k) * (↑m / (↑m + ↑k)))(sum_neg_pow_mul_distrib :  ∑ k in Ico 1 n, (-1 : ℝ) ^ k * (↑(Nat.choose (n - 1) k) + ↑(Nat.choose (n - 1) (k - 1))) * (m / (m + ↑k)) =    ∑ k in Ico 1 n, ((-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) + (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1))) * (m / (m + ↑k)))(gol:  ∑ k in Ico 1 n, ((-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) + (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1))) * (m / (m + ↑k)) =
    ∑ k in Ico 1 n,
      ((-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) + (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)))) :
   ∑ k in Ico 1 n, (-1 : ℝ) ^ k * (↑(Nat.choose (n - 1) k) + ↑(Nat.choose (n - 1) (k - 1))) * (m / (m + ↑k)) =
    ∑ k in Ico 1 n,
      ((-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) + (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k))) := by
  rw[sum_neg_pow_mul_distrib]
  apply gol

theorem sum_neg_pow_mul_mul_from_3_to_3(n : ℕ)(m : ℝ)(t : optParam (ℕ → ℕ → ℕ → ℝ) fun m n k => (-1 : ℝ) ^ k * ↑(Nat.choose n k) * (↑m / (↑m + ↑k)))(sum_neg_pow_mul_distrib :  ∑ k in Ico 1 n, (-1 : ℝ) ^ k * (↑(Nat.choose (n - 1) k) + ↑(Nat.choose (n - 1) (k - 1))) * (m / (m + ↑k)) =    ∑ k in Ico 1 n, ((-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) + (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1))) * (m / (m + ↑k)))(y : ℕ)(x✝ : y ∈ Ico 1 n) :
   ((-1 : ℝ) ^ y * ↑(Nat.choose (n - 1) y) + (-1 : ℝ) ^ y * ↑(Nat.choose (n - 1) (y - 1))) * (m / (m + ↑y)) =
    (-1 : ℝ) ^ y * ↑(Nat.choose (n - 1) y) * (m / (m + ↑y)) + (-1 : ℝ) ^ y * ↑(Nat.choose (n - 1) (y - 1)) * (m / (m + ↑y)) := by
  rw[add_mul]

