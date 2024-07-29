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


theorem sum_neg_pow_mul_div_succ_congr_from_0_to_0(n : ℕ)(gol:  ∑ x in range (n + 1), (-1 : ℝ) ^ x * (↑x + 1)⁻¹ * ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ x in range (n + 1), (-1 : ℝ) ^ (1 + x + 1) * (1 + ↑x)⁻¹ * ↑(Nat.choose (n + 1) (1 + x))) :
   ∑ x in range (n + 1), (-1 : ℝ) ^ x * (1 / (↑x + 1)) * ↑(Nat.choose (n + 1) (x + 1)) =
    ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ (1 + x + 1) * (1 / (1 + ↑x)) * ↑(Nat.choose (n + 1) (1 + x)) := by
  simp
  apply gol

theorem sum_neg_pow_mul_div_succ_congr_from_7_to_7(n y : ℕ)(x✝ : y ∈ range (n + 1))(gol:  Nat.choose (n + 1) (y + 1) = Nat.choose (n + 1) (1 + y)) :
   Nat.choose (n + 1) (y + 1) = Nat.choose (n + 1) (1 + y) := by
  have h3: Nat.choose (n + 1) (y + 1) = Nat.choose (n + 1) (1 + y) := by rw[add_comm y 1]
  apply gol

theorem sum_neg_pow_mul_div_succ_congr_from_7_to_8(n y : ℕ)(x✝ : y ∈ range (n + 1)) :
   Nat.choose (n + 1) (y + 1) = Nat.choose (n + 1) (1 + y) := by
  have h3: Nat.choose (n + 1) (y + 1) = Nat.choose (n + 1) (1 + y) := by rw[add_comm y 1]
  exact h3

theorem sum_neg_pow_mul_div_succ_congr_from_8_to_8(n y : ℕ)(x✝ : y ∈ range (n + 1))(h3 : Nat.choose (n + 1) (y + 1) = Nat.choose (n + 1) (1 + y)) :
   Nat.choose (n + 1) (y + 1) = Nat.choose (n + 1) (1 + y) := by
  exact h3

