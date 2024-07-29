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


theorem odd_choose_from_0_to_0(n m : ℕ)(hnm : n = 2 * m + 1)(gol:  1 / (2 * ↑m + 1) * ∑ l in Ico 0 (2 * m), (↑l + 1) * (-1 : ℝ) ^ (l + 1) / ↑(Nat.choose (2 * m) l) = 0) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = 0 := by
  rw[odd_choose_sum hnm , Ico_even_odd, Ico_div]
  apply gol

theorem odd_choose_from_0_to_1(n m : ℕ)(hnm : n = 2 * m + 1) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = 0 := by
  rw[odd_choose_sum hnm , Ico_even_odd, Ico_div]
  rw[div_mul_Ico_eq_zero]

theorem odd_choose_from_1_to_1(n m : ℕ)(hnm : n = 2 * m + 1) :
   1 / (2 * ↑m + 1) * ∑ l in Ico 0 (2 * m), (↑l + 1) * (-1 : ℝ) ^ (l + 1) / ↑(Nat.choose (2 * m) l) = 0 := by
  rw[div_mul_Ico_eq_zero]

