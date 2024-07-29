import Theorem.example_separate.choose_mul_eq_mul_sub_div
import Theorem.example_separate.Ico_pow_choose
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum

open Nat
open Finset
open BigOperators


theorem idt46 {n k: ℕ}: ∑ k in range (n+1), ((-1 : ℝ) ^ k) * (1 / ((k + 1)) : ℝ ) * ((1 / ((k + 1)) : ℝ )) * choose n k = 1 / (n+1) * ∑ k in range (n+1), 1 / (k+1)  := by
  have t13: ∑ k in range (n+1), ((-1 : ℝ) ^ k) * (1 / ((k + 1)) : ℝ ) * ((1 / ((k + 1)) : ℝ )) * choose n k =
   ∑ k in range (n+1), (1/(n+1)) * (((-1 : ℝ) ^ k) * (1 / ((k + 1)) : ℝ ) * choose (n+1) (k+1)) := by
    refine' sum_congr rfl fun y hy => _
    rw[mul_assoc, choose_mul_eq_mul_sub_div, ← mul_assoc]
    rw[mul_comm ((-1 : ℝ) ^ y * (1 / (↑y + 1))) (1 / (n + 1))]
    rw[← mul_assoc]
    rw[mul_assoc, mul_assoc,mul_assoc]
  rw[t13]
  rw[← mul_sum]
  congr 1
  have sum_neg_pow_div_congr : ∑ x in Ico 1 (n + 2), (-1 : ℝ) ^ (x+1) * (1 / x) * (Nat.choose (n + 1) x) =
   ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ ( 1 + x + 1 ) * (1 / (1 + x)) * (Nat.choose (n + 1) (1 + x)) := by
    rw[sum_Ico_eq_sum_range]
    simp
  have pow_neg_succ_succ : ∑ x in range (n + 1), (-1 : ℝ) ^ x * (1 / (x + 1)) * (Nat.choose (n + 1) (x + 1)) =
   ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ ( 1 + x + 1 ) * (1 / (1 + x)) * (Nat.choose (n + 1) (1 + x)) := by
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
  rw[pow_neg_succ_succ, ← sum_neg_pow_div_congr]
  rw[Ico_pow_choose]
