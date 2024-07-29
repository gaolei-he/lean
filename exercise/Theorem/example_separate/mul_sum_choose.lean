import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat

open Finset

open BigOperators

theorem mul_sum_choose : (2 * n + 1) * ∑ k in range n, ((choose (2*n) k):ℝ) = (2 * n + 1) * ((∑ k in range (n+1), ((choose (2*n) k):ℝ)) - ((choose (2*n) n):ℝ) ) := by
  congr 1
  rw[sum_range_succ]
  simp


theorem mul_sum_choose_from_1_to_1(n : ℕ)(gol:  ∑ k in range n, ↑(Nat.choose (2 * n) k) =
    ∑ x in range n, ↑(Nat.choose (2 * n) x) + ↑(Nat.choose (2 * n) n) - ↑(Nat.choose (2 * n) n)) :
   ∑ k in range n, ↑(Nat.choose (2 * n) k) = ∑ k in range (n + 1), ↑(Nat.choose (2 * n) k) - ↑(Nat.choose (2 * n) n) := by
  rw[sum_range_succ]
  apply gol

theorem mul_sum_choose_from_1_to_2(n : ℕ) :
   ∑ k in range n, ↑(Nat.choose (2 * n) k) = ∑ k in range (n + 1), ↑(Nat.choose (2 * n) k) - ↑(Nat.choose (2 * n) n) := by
  rw[sum_range_succ]
  simp

theorem mul_sum_choose_from_2_to_2(n : ℕ) :
   ∑ k in range n, ↑(Nat.choose (2 * n) k) =
    ∑ x in range n, ↑(Nat.choose (2 * n) x) + ↑(Nat.choose (2 * n) n) - ↑(Nat.choose (2 * n) n) := by
  simp

