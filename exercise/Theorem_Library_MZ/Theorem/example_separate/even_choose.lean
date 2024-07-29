import Theorem.example_separate.two_even_congr
import Theorem.example_separate.two_congr
import Theorem.example_separate.add_neg_div

open Nat

open Finset

open BigOperators

theorem even_choose(hnm: n = 2 * m)(hm : 0 < m) : ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = 2 * (n + 1) / (n + 2) := by
  rw[two_even_congr hnm hm]
  rw[two_congr]
  rw[add_neg_div hm]
  have mul_two_div_mul : (2 * (m : ℝ) + 1) / (((m : ℝ) + 1)) * (1/2) = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1/2) := by
      rw[← div_eq_mul_one_div]
      rw[div_div]
      rw[add_mul, mul_comm (m : ℝ) 2]
      simp
      rw[← mul_div]
      rw[mul_right_comm]
      simp
      rw[hnm]
      rw[cast_mul]
      simp
  simp at mul_two_div_mul
  rw[mul_two_div_mul]


theorem even_choose_from_2_to_2(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2)) :
   2 + -1 / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2) := by
  rw[add_neg_div hm]
  apply gol

theorem even_choose_from_2_to_3(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2)) :
   2 + -1 / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2) := by
  rw[add_neg_div hm]
  have mul_two_div_mul : (2 * (m : ℝ) + 1) / (((m : ℝ) + 1)) * (1/2) = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1/2) := by
      rw[← div_eq_mul_one_div]
      rw[div_div]
      rw[add_mul, mul_comm (m : ℝ) 2]
      simp
      rw[← mul_div]
      rw[mul_right_comm]
      simp
      rw[hnm]
      rw[cast_mul]
      simp
  apply gol

theorem even_choose_from_2_to_4(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2)) :
   2 + -1 / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2) := by
  rw[add_neg_div hm]
  have mul_two_div_mul : (2 * (m : ℝ) + 1) / (((m : ℝ) + 1)) * (1/2) = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1/2) := by
      rw[← div_eq_mul_one_div]
      rw[div_div]
      rw[add_mul, mul_comm (m : ℝ) 2]
      simp
      rw[← mul_div]
      rw[mul_right_comm]
      simp
      rw[hnm]
      rw[cast_mul]
      simp
  simp at mul_two_div_mul
  apply gol

theorem even_choose_from_2_to_5(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m) :
   2 + -1 / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2) := by
  rw[add_neg_div hm]
  have mul_two_div_mul : (2 * (m : ℝ) + 1) / (((m : ℝ) + 1)) * (1/2) = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1/2) := by
      rw[← div_eq_mul_one_div]
      rw[div_div]
      rw[add_mul, mul_comm (m : ℝ) 2]
      simp
      rw[← mul_div]
      rw[mul_right_comm]
      simp
      rw[hnm]
      rw[cast_mul]
      simp
  simp at mul_two_div_mul
  rw[mul_two_div_mul]

theorem even_choose_from_3_to_3(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2)) :
   (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2) := by
  have mul_two_div_mul : (2 * (m : ℝ) + 1) / (((m : ℝ) + 1)) * (1/2) = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1/2) := by
      rw[← div_eq_mul_one_div]
      rw[div_div]
      rw[add_mul, mul_comm (m : ℝ) 2]
      simp
      rw[← mul_div]
      rw[mul_right_comm]
      simp
      rw[hnm]
      rw[cast_mul]
      simp
  apply gol

theorem even_choose_from_3_to_4(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(gol:  (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2)) :
   (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2) := by
  have mul_two_div_mul : (2 * (m : ℝ) + 1) / (((m : ℝ) + 1)) * (1/2) = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1/2) := by
      rw[← div_eq_mul_one_div]
      rw[div_div]
      rw[add_mul, mul_comm (m : ℝ) 2]
      simp
      rw[← mul_div]
      rw[mul_right_comm]
      simp
      rw[hnm]
      rw[cast_mul]
      simp
  simp at mul_two_div_mul
  apply gol

theorem even_choose_from_3_to_5(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m) :
   (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2) := by
  have mul_two_div_mul : (2 * (m : ℝ) + 1) / (((m : ℝ) + 1)) * (1/2) = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1/2) := by
      rw[← div_eq_mul_one_div]
      rw[div_div]
      rw[add_mul, mul_comm (m : ℝ) 2]
      simp
      rw[← mul_div]
      rw[mul_right_comm]
      simp
      rw[hnm]
      rw[cast_mul]
      simp
  simp at mul_two_div_mul
  rw[mul_two_div_mul]

theorem even_choose_from_4_to_4(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(mul_two_div_mul : (2 * ↑m + 1) / (↑m + 1) * (1 / 2) = 2 * (↑n + 1) / (↑n + 2) * (1 / 2))(gol:  (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2)) :
   (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2) := by
  simp at mul_two_div_mul
  apply gol

theorem even_choose_from_4_to_5(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(mul_two_div_mul : (2 * ↑m + 1) / (↑m + 1) * (1 / 2) = 2 * (↑n + 1) / (↑n + 2) * (1 / 2)) :
   (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2) := by
  simp at mul_two_div_mul
  rw[mul_two_div_mul]

theorem even_choose_from_5_to_5(n m : ℕ)(hnm : n = 2 * m)(hm : 0 < m)(mul_two_div_mul : (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2)) :
   (2 * ↑m + 1) / (↑m + 1) = 2 * (↑n + 1) / (↑n + 2) := by
  rw[mul_two_div_mul]

