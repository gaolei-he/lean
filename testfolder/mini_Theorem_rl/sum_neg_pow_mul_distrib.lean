import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem sum_neg_pow_mul_distrib: ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (((-1 : ℝ)^k * choose (n-1) k + (-1 : ℝ)^k * choose (n-1) (k-1)) : ℝ) * (m / (m+k)) := by lean_repl sorry
    refine' sum_congr rfl fun y _ => _
    rw[mul_add]
