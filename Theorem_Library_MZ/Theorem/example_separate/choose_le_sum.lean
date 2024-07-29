import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators


theorem choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
      rw[sum_range_succ]
      simp


theorem choose_le_sum_from_0_to_0(n : ℕ)(gol:  Nat.choose (2 * n) n ≤ ∑ x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n) :
   Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k := by
  rw[sum_range_succ]
  apply gol

theorem choose_le_sum_from_0_to_1(n : ℕ) :
   Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k := by
  rw[sum_range_succ]
  simp

theorem choose_le_sum_from_1_to_1(n : ℕ) :
   Nat.choose (2 * n) n ≤ ∑ x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n := by
  simp

