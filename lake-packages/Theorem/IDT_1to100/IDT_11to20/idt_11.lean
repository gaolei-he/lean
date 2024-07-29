import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Theorem.example_separate.choose_mul_eq_mul_sub
import Theorem.example_separate.choose_eq_choose_add
import Mathlib.Data.Nat.Choose.Sum

open Nat

theorem choose_eq_choose_add'(h1:1 ≤ n)(h2:1 ≤ k) : choose n k = choose (n-1) (k-1) + choose (n-1) k := by
  have h3: choose n k = choose (n-1) k  + choose (n-1) (k-1) := by
    exact choose_eq_choose_add h1 h2
  linarith

theorem Identity_11 {n k: ℕ} (h1 : k ≥ 1) (h2 :k ≤ n - 1) : n * choose n k = k * choose n k + (k + 1) * choose n (k + 1) := by
  have h3: choose n k * k = n * choose (n - 1) (k - 1) := by
    refine choose_mul_eq_mul_sub ?hkn h1
    have c1 : n - 1 ≤ n := by
      exact sub_le n 1
    exact Nat.le_trans h2 c1
  have h4: choose n (k + 1) * (k + 1) = n * choose (n - 1) k := by
    have c2 : 1 ≤ k + 1 := by
      exact Nat.le_add_left 1 k
    have c3 : k + 1 ≤ n := by
      rwa [← le_tsub_iff_right]
      rw [Nat.one_le_iff_ne_zero]
      intro b
      rw[b] at h2
      simp at h2
      rw[h2] at h1
      linarith
    apply choose_mul_eq_mul_sub
    · exact c3
    · exact c2
  have h6: choose n k = choose (n - 1) (k - 1) + choose (n - 1) k := by
    have c4 : 1 ≤ n - 1 := by
      exact Nat.le_trans h1 h2
    have d1 : n - 1 ≤ n := by exact sub_le n 1
    have d2 : 1 ≤ n := by exact Nat.le_trans c4 d1
    have c5 : 1 ≤ k := by
      exact h1
    apply choose_eq_choose_add'
    · exact d2
    · exact c5
  have h7: n * choose n k = n *(choose (n - 1) (k - 1) + choose (n - 1) k) := by
    exact congrArg (HMul.hMul n) h6
  linarith
