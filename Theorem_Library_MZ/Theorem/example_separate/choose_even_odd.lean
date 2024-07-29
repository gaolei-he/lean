import Theorem.example_separate.even_choose
import Theorem.example_separate.odd_choose
import Mathlib.Data.Nat.Parity

open Nat

open Finset

open BigOperators


theorem choose_even_odd(h: 0 < n): ∑ k in range (n+1), (-1 : ℝ ) ^ k / choose n k = (n + 1)/(n + 2) * (1 + (-1)^n) := by
  rcases Nat.even_or_odd' n with ⟨m, h1 | h2⟩
  · have hm : 0 < m := by linarith
    rw[even_choose h1 hm]
    have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
    rw[m_two]
    rw[Even.neg_one_pow ⟨m, rfl⟩]
    norm_num
    rw[mul_div_assoc, mul_comm]
  · rw[odd_choose h2]
    rw[h2, Odd.neg_one_pow ⟨m, rfl⟩]
    norm_num


theorem choose_even_odd_from_1_to_1(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(gol:  ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have hm : 0 < m := by linarith
  apply gol

theorem choose_even_odd_from_1_to_2(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have hm : 0 < m := by linarith
  rw[even_choose h1 hm]
  apply gol

theorem choose_even_odd_from_1_to_3(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have hm : 0 < m := by linarith
  rw[even_choose h1 hm]
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  apply gol

theorem choose_even_odd_from_1_to_4(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ (m + m))) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have hm : 0 < m := by linarith
  rw[even_choose h1 hm]
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  apply gol

theorem choose_even_odd_from_1_to_5(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + 1)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have hm : 0 < m := by linarith
  rw[even_choose h1 hm]
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  apply gol

theorem choose_even_odd_from_1_to_6(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * 2) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have hm : 0 < m := by linarith
  rw[even_choose h1 hm]
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  norm_num
  apply gol

theorem choose_even_odd_from_1_to_7(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have hm : 0 < m := by linarith
  rw[even_choose h1 hm]
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  norm_num
  rw[mul_div_assoc, mul_comm]

theorem choose_even_odd_from_2_to_2(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  rw[even_choose h1 hm]
  apply gol

theorem choose_even_odd_from_2_to_3(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  rw[even_choose h1 hm]
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  apply gol

theorem choose_even_odd_from_2_to_4(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ (m + m))) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  rw[even_choose h1 hm]
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  apply gol

theorem choose_even_odd_from_2_to_5(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + 1)) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  rw[even_choose h1 hm]
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  apply gol

theorem choose_even_odd_from_2_to_6(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * 2) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  rw[even_choose h1 hm]
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  norm_num
  apply gol

theorem choose_even_odd_from_2_to_7(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m) :
   ∑ k in range (n + 1), (-1 : ℝ) ^ k / ↑(Nat.choose n k) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  rw[even_choose h1 hm]
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  norm_num
  rw[mul_div_assoc, mul_comm]

theorem choose_even_odd_from_3_to_3(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n)) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  apply gol

theorem choose_even_odd_from_3_to_4(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ (m + m))) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  apply gol

theorem choose_even_odd_from_3_to_5(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + 1)) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  apply gol

theorem choose_even_odd_from_3_to_6(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * 2) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  norm_num
  apply gol

theorem choose_even_odd_from_3_to_7(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  have m_two : (-1 : ℝ ) ^ n = (-1 : ℝ ) ^ (m + m) := by rw[h1, two_mul]
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  norm_num
  rw[mul_div_assoc, mul_comm]

theorem choose_even_odd_from_4_to_4(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(m_two : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (m + m))(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ (m + m))) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  rw[m_two]
  apply gol

theorem choose_even_odd_from_4_to_5(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(m_two : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (m + m))(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + 1)) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  apply gol

theorem choose_even_odd_from_4_to_6(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(m_two : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (m + m))(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * 2) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  norm_num
  apply gol

theorem choose_even_odd_from_4_to_7(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(m_two : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (m + m)) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ n) := by
  rw[m_two]
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  norm_num
  rw[mul_div_assoc, mul_comm]

theorem choose_even_odd_from_5_to_5(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(m_two : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (m + m))(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + 1)) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ (m + m)) := by
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  apply gol

theorem choose_even_odd_from_5_to_6(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(m_two : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (m + m))(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * 2) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ (m + m)) := by
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  norm_num
  apply gol

theorem choose_even_odd_from_5_to_7(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(m_two : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (m + m)) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + (-1 : ℝ) ^ (m + m)) := by
  rw[Even.neg_one_pow ⟨m, rfl⟩]
  norm_num
  rw[mul_div_assoc, mul_comm]

theorem choose_even_odd_from_6_to_6(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(m_two : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (m + m))(gol:  2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * 2) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + 1) := by
  norm_num
  apply gol

theorem choose_even_odd_from_6_to_7(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(m_two : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (m + m)) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * (1 + 1) := by
  norm_num
  rw[mul_div_assoc, mul_comm]

theorem choose_even_odd_from_7_to_7(n : ℕ)(h : 0 < n)(m : ℕ)(h1 : n = 2 * m)(hm : 0 < m)(m_two : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (m + m)) :
   2 * (↑n + 1) / (↑n + 2) = (↑n + 1) / (↑n + 2) * 2 := by
  rw[mul_div_assoc, mul_comm]

