import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases

open Nat

open Finset

open BigOperators

variable {R : Type*}

theorem sum_binomial_squared (n : ℕ)(hn: n = 1 ∨ n = 2) :
  ∑ k in range (n + 1), ((choose n k):ℝ) * ((k:ℝ)^2) * (-1:ℝ )^k = (-1:ℝ)^n * n ! := by
  cases' hn with hn1 hn2
  · rw[hn1,factorial_one]
    simp
    rw[sum_range_succ_comm,sum_range_succ_comm]
    simp
  · rw[hn2,factorial_two]
    simp
    rw[sum_range_succ_comm,sum_range_succ_comm]
    simp
    norm_num
