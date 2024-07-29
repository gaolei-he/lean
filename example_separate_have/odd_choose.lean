import Theorem.example_separate.odd_choose_sum
import Theorem.example_separate.Ico_even_odd
import Theorem.example_separate.Ico_div
import Theorem.example_separate.div_mul_Ico_eq_zero

open Nat

open Finset

open BigOperators

theorem odd_choose (hnm: n = 2 * m + 1) : ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = 0 := by
    rw[odd_choose_sum hnm , Ico_even_odd, Ico_div]
    rw[div_mul_Ico_eq_zero]
