import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_neg_pow_mul_add( hn: 0 < n):
∑ k in Ico 1 n, (-1 : ℝ) ^ k * ((Nat.choose (n - 1) (k - 1)) : ℝ) * (m / (m + k)) + (-1 : ℝ)^n * (choose n n : ℝ) * (m / (m+n)) = ∑ k in Ico 1 (n+1), (-1 : ℝ) ^ k * ((Nat.choose (n - 1) (k - 1)) : ℝ) * (m / (m + k)) := by
  have h1:  1 ≤ n := by linarith
  rw[sum_Ico_succ_top h1]
  simp


theorem sum_neg_pow_mul_add_from_0_to_0(n : ℕ)(m : ℝ)(hn : 0 < n)(gol:  ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose n n) * (m / (m + ↑n)) =
    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k))) :
   ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose n n) * (m / (m + ↑n)) =
    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) := by
  have h1:  1 ≤ n := by linarith
  apply gol

theorem sum_neg_pow_mul_add_from_0_to_1(n : ℕ)(m : ℝ)(hn : 0 < n)(gol:  ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose n n) * (m / (m + ↑n)) =
    ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose (n - 1) (n - 1)) * (m / (m + ↑n))) :
   ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose n n) * (m / (m + ↑n)) =
    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) := by
  have h1:  1 ≤ n := by linarith
  rw[sum_Ico_succ_top h1]
  apply gol

theorem sum_neg_pow_mul_add_from_0_to_2(n : ℕ)(m : ℝ)(hn : 0 < n) :
   ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose n n) * (m / (m + ↑n)) =
    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) := by
  have h1:  1 ≤ n := by linarith
  rw[sum_Ico_succ_top h1]
  simp

theorem sum_neg_pow_mul_add_from_1_to_1(n : ℕ)(m : ℝ)(hn : 0 < n)(h1 : 1 ≤ n)(gol:  ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose n n) * (m / (m + ↑n)) =
    ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose (n - 1) (n - 1)) * (m / (m + ↑n))) :
   ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose n n) * (m / (m + ↑n)) =
    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) := by
  rw[sum_Ico_succ_top h1]
  apply gol

theorem sum_neg_pow_mul_add_from_1_to_2(n : ℕ)(m : ℝ)(hn : 0 < n)(h1 : 1 ≤ n) :
   ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose n n) * (m / (m + ↑n)) =
    ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) := by
  rw[sum_Ico_succ_top h1]
  simp

theorem sum_neg_pow_mul_add_from_2_to_2(n : ℕ)(m : ℝ)(hn : 0 < n)(h1 : 1 ≤ n) :
   ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose n n) * (m / (m + ↑n)) =
    ∑ k in Ico 1 n, (-1 : ℝ) ^ k * ↑(Nat.choose (n - 1) (k - 1)) * (m / (m + ↑k)) +
      (-1 : ℝ) ^ n * ↑(Nat.choose (n - 1) (n - 1)) * (m / (m + ↑n)) := by
  simp

