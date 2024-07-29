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
