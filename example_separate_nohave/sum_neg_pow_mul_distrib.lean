import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_neg_pow_mul_distrib: ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (((-1 : ℝ)^k * choose (n-1) k + (-1 : ℝ)^k * choose (n-1) (k-1)) : ℝ) * (m / (m+k)) := by
    refine' sum_congr rfl fun y _ => _
    rw[mul_add]
