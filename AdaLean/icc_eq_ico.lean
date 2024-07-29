import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem icc_eq_ico
(n : ℕ)
(h₀ : 0 < n) :
∑ k in Finset.Icc 1 n, (k * Nat.choose n k) = ∑ k in Ico 0 (n+1), (k * Nat.choose n k):= by
  rw [sum_eq_sum_Ico_succ_bot]
  simp
  exact rfl
  linarith
