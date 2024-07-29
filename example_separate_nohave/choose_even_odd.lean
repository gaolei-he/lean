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
