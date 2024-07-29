import Theorem.example_separate.sum_neg_pow_mul_mul

open Nat

open Finset

open BigOperators

theorem sum_neg_pow_mul_eq_sum_distrib(t : ℕ → ℕ → ℕ → ℝ := fun m n k => (-1 : ℝ)^k * (choose n k : ℝ) * (m / (m+k))):
  ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, ((-1 : ℝ)^k * choose (n-1) k * (m / (m+k))) + ∑ k in Ico 1 n, ((-1 : ℝ)^k * choose (n-1) (k-1) * (m / (m+k)) : ℝ):= by
  rw[sum_neg_pow_mul_mul]
  rw[sum_add_distrib]


theorem sum_neg_pow_mul_eq_sum_distrib_from_0_to_0(n : ℕ)(m : ℝ)(t : optParam (ℕ → ℕ → ℕ → ℝ) fun m n k => (-1 : ℝ) ^ k * ↑(Nat.choose n k) * (↑m / (↑m + ↑k)))(gol:  ∑ k in Ico 1 n,
      ((-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) +
        (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k))) =
    ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) +
      ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k))) :
   ∑ k in Ico 1 n, (-1 : ℝ) ^ k * (↑(Nat.choose (n - 1) k) + ↑(Nat.choose (n - 1) (k - 1))) * (m / (m + ↑k)) =
    ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) +
      ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) := by
  rw[sum_neg_pow_mul_mul]
  apply gol

theorem sum_neg_pow_mul_eq_sum_distrib_from_0_to_1(n : ℕ)(m : ℝ)(t : optParam (ℕ → ℕ → ℕ → ℝ) fun m n k => (-1 : ℝ) ^ k * ↑(Nat.choose n k) * (↑m / (↑m + ↑k))) :
   ∑ k in Ico 1 n, (-1 : ℝ) ^ k * (↑(Nat.choose (n - 1) k) + ↑(Nat.choose (n - 1) (k - 1))) * (m / (m + ↑k)) =
    ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) +
      ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) := by
  rw[sum_neg_pow_mul_mul]
  rw[sum_add_distrib]

theorem sum_neg_pow_mul_eq_sum_distrib_from_1_to_1(n : ℕ)(m : ℝ)(t : optParam (ℕ → ℕ → ℕ → ℝ) fun m n k => (-1 : ℝ) ^ k * ↑(Nat.choose n k) * (↑m / (↑m + ↑k))) :
   ∑ k in Ico 1 n,
      ((-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) +
        (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k))) =
    ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) +
      ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) := by
  rw[sum_add_distrib]

