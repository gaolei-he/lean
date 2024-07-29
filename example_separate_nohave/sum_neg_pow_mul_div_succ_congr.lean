import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Finset

open BigOperators

theorem sum_neg_pow_mul_div_succ_congr : ∑ x in range (n + 1), (-1 : ℝ) ^ x * (1 / (x + 1)) * (Nat.choose (n + 1) (x + 1)) = ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ ( 1 + x + 1 ) * (1 / (1 + x)) * (Nat.choose (n + 1) (1 + x)) := by
  simp
  refine' sum_congr rfl fun y _ => _
  congr 2
  have h1: (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + y + 1) := by
    rw[add_comm, ← add_assoc]
    norm_num
    rw[pow_add]
    simp
  exact h1
  have h2: ((y + 1): ℝ)⁻¹ = ((1 + y): ℝ)⁻¹ := by rw[add_comm]
  exact h2
  have h3: Nat.choose (n + 1) (y + 1) = Nat.choose (n + 1) (1 + y) := by rw[add_comm y 1]
  exact h3
