import Mathlib.Data.Real.Basic
import Theorem.example_separate.add_two_sub

open Nat

open Finset

open BigOperators

theorem Transit_item: ∑ k in Ico (2*n + 1 - n) (2 * n + 1 - 1), (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ)) =
        ∑ k in Ico (n+1) (2 * n), (-1 : ℝ) ^ (k - 1) * ((n - k)/(choose (2*n) k : ℝ)) := by
        rw[add_two_sub]
        simp


theorem Transit_item_from_0_to_0(n : ℕ)(gol:  ∑ k in Ico (n + 1) (2 * n + 1 - 1), (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) =
    ∑ k in Ico (n + 1) (2 * n), (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k))) :
   ∑ k in Ico (2 * n + 1 - n) (2 * n + 1 - 1), (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) =
    ∑ k in Ico (n + 1) (2 * n), (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) := by
  rw[add_two_sub]
  apply gol

theorem Transit_item_from_0_to_1(n : ℕ) :
   ∑ k in Ico (2 * n + 1 - n) (2 * n + 1 - 1), (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) =
    ∑ k in Ico (n + 1) (2 * n), (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) := by
  rw[add_two_sub]
  simp

theorem Transit_item_from_1_to_1(n : ℕ) :
   ∑ k in Ico (n + 1) (2 * n + 1 - 1), (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) =
    ∑ k in Ico (n + 1) (2 * n), (-1 : ℝ) ^ (k - 1) * ((↑n - ↑k) / ↑(Nat.choose (2 * n) k)) := by
  simp

