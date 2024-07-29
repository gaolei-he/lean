import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators


theorem Identity_22_2{n : ℕ} (h2 : n ≠ 0) :  (∑ k in range (n + 1), ((-1) ^ k * ↑(choose n k) : ℤ)) * k = 0 := by
  have c1:(∑ k in range (n + 1), ((-1) ^ k * ↑(choose n k) : ℤ)) = 0 := by
    rw [Int.alternating_sum_range_choose, if_neg h2]
  have c2: 0 * k = 0 :=by
    linarith
  exact mul_eq_zero_of_left c1 k
