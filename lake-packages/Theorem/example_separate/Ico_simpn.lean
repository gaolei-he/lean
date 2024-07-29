import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat

open Finset

open BigOperators


theorem Ico_simpn (hn : 1 ≤ n): ∑ k in Ico 1 (n+1), (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ)) =
   ∑ k in Ico 1 n, (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ) ) := by
    rw [sum_Ico_succ_top hn]
    simp


theorem Ico_simpn_from_0_to_0(n : ℕ)(hn : 1 ≤ n)(gol:  ∑ k in Ico 1 n, (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) +
      (-1 : ℝ) ^ (n - 1) * ((↑n - ↑n) / ↑(Nat.choose (2 * n) n)) =
    ∑ k in Ico 1 n, (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k))) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) =
    ∑ k in Ico 1 n, (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) := by
  rw [sum_Ico_succ_top hn]
  apply gol

theorem Ico_simpn_from_0_to_1(n : ℕ)(hn : 1 ≤ n) :
   ∑ k in Ico 1 (n + 1), (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) =
    ∑ k in Ico 1 n, (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) := by
  rw [sum_Ico_succ_top hn]
  simp

theorem Ico_simpn_from_1_to_1(n : ℕ)(hn : 1 ≤ n) :
   ∑ k in Ico 1 n, (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) +
      (-1 : ℝ) ^ (n - 1) * ((↑n - ↑n) / ↑(Nat.choose (2 * n) n)) =
    ∑ k in Ico 1 n, (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) := by
  simp

