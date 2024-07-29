import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators


theorem Identity_22_1(h1 : n = 1): ∑ k in range (n + 1), ((-1) ^ k * k *↑ (choose n k) : ℤ) = -1 := by
  have c0: n = 1 := by
   exact h1
  have c1(h2:n = 1): ∑ k in range (n + 1), ((-1) ^ k * k * ↑ (choose n k) : ℤ) = ∑ k in range (1 + 1), ((-1) ^ k * k * ↑ (choose 1 k) : ℤ) := by
    rw[c0]
  have c2:∑ k in range (1 + 1), ((-1) ^ k * k * ↑ (choose 1 k) : ℤ) = ((-1) ^ 0 * 0 * ↑ (choose 1 0) : ℤ) + ((-1) ^ 1 * 1 * ↑ (choose 1 1) : ℤ):= by
    exact rfl
  have c3:((-1) ^ 0 * 0 * ↑ (choose 1 0) : ℤ) = 0 := by
    have d1: choose 1 0 = 1 := by
      exact rfl
    have d2: (-1)^ 0 * 0 * 1 = 0:=by
      exact rfl
    have d3: ((-1)^ 0 * 0 * ↑ (choose 1 0) : ℤ) = (-1)^ 0 * 0 * 1:=by
      exact d2
    linarith
  have c4:((-1) ^ 1 * 1 * ↑ (choose 1 1) : ℤ) = -1 := by
    have d4: choose 1 1 = 1 := by
      exact rfl
    have d5: (-1)^ 1 * 1 * 1 = -1 := by
      exact rfl
    have d6:((-1) ^ 1 * 1 * ↑ (choose 1 1) : ℤ) = (-1)^ 1 * 1 * 1 := by
      exact c2
    linarith
  exact c1 h1
