import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem sum_neg_pow_mul_add( hn: 0 < n):
∑ k in Ico 1 n, (-1 : ℝ) ^ k * ((Nat.choose (n - 1) (k - 1)) : ℝ) * (m / (m + k)) + (-1 : ℝ)^n * (choose n n : ℝ) * (m / (m+n)) = ∑ k in Ico 1 (n+1), (-1 : ℝ) ^ k * ((Nat.choose (n - 1) (k - 1)) : ℝ) * (m / (m + k)) := by lean_repl sorry
  rw[sum_Ico_succ_top]
  simp
  linarith
