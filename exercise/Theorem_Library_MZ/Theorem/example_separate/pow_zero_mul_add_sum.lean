import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem pow_zero_mul_add_sum( hn: 0 < n):
((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico 1 n, (-1 : ℝ)^k * (choose (n-1) k : ℝ) * (m / (m+k))) =
∑ k in range n, (-1 : ℝ)^k * (choose (n-1) k : ℝ) * (m / (m+k)) := by
  have h_pow_zero_mul_add: ((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k) : ℝ) * (m / (m+k))) = ((-1 : ℝ)^0 * (choose (n-1) 0 : ℝ) * (m / (m+0)) + ∑ k in Ico (0+1) n, (-1 : ℝ)^k * ((choose (n-1) k) : ℝ) * (m / (m+k))):= by
    congr 1
  rw[h_pow_zero_mul_add, range_eq_Ico, sum_eq_sum_Ico_succ_bot hn]
  simp


theorem pow_zero_mul_add_sum_from_1_to_1(n : ℕ)(m : ℝ)(hn : 0 < n)(h_pow_zero_mul_add :  (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +      ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) =    (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +      ∑ k in Ico (0 + 1) n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)))(gol:  (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +
      ∑ k in Ico (0 + 1) n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) =
    (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + ↑0)) +
      ∑ k in Ico (0 + 1) n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k))) :
   (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +
      ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) =
    ∑ k in range n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) := by
  rw[h_pow_zero_mul_add, range_eq_Ico, sum_eq_sum_Ico_succ_bot hn]
  apply gol

theorem pow_zero_mul_add_sum_from_1_to_2(n : ℕ)(m : ℝ)(hn : 0 < n)(h_pow_zero_mul_add :  (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +      ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) =    (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +      ∑ k in Ico (0 + 1) n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k))) :
   (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +
      ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) =
    ∑ k in range n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) := by
  rw[h_pow_zero_mul_add, range_eq_Ico, sum_eq_sum_Ico_succ_bot hn]
  simp

theorem pow_zero_mul_add_sum_from_2_to_2(n : ℕ)(m : ℝ)(hn : 0 < n)(h_pow_zero_mul_add :  (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +      ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) =    (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +      ∑ k in Ico (0 + 1) n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k))) :
   (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + 0)) +
      ∑ k in Ico (0 + 1) n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) =
    (-1 : ℝ) ^ 0 * ↑(Nat.choose (n - 1) 0) * (m / (m + ↑0)) +
      ∑ k in Ico (0 + 1) n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) k) * (m / (m + ↑k)) := by
  simp

