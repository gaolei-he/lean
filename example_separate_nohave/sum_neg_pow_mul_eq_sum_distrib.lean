import Theorem.example_separate.sum_neg_pow_mul_mul

open Nat

open Finset

open BigOperators

theorem sum_neg_pow_mul_eq_sum_distrib(t : ℕ → ℕ → ℕ → ℝ := fun m n k => (-1 : ℝ)^k * (choose n k : ℝ) * (m / (m+k))):
  ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, ((-1 : ℝ)^k * choose (n-1) k * (m / (m+k))) + ∑ k in Ico 1 n, ((-1 : ℝ)^k * choose (n-1) (k-1) * (m / (m+k)) : ℝ):= by
  rw[sum_neg_pow_mul_mul]
  rw[sum_add_distrib]
