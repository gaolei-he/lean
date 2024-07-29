import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem add_pow_sub_choose_of_ne {n : ℕ} (h : n ≠ 0) : ∑ k in range (n+1), ((choose n k - (-1)^k * choose n k) : ℤ) = 2^n := by
  rw [sum_sub_distrib]
  rw [Int.alternating_sum_range_choose_of_ne h]
  simp
  have := (add_pow (1:ℤ) 1 n).symm
  simpa [one_add_one_eq_two] using this
