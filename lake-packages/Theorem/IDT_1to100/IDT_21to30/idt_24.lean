import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub_div

open Nat
open Finset
open BigOperators


theorem idt_24 {n: ℕ}:
 ∑ k in range (n+1), ((-1:ℝ)^k)*(((1/(k+1)) : ℝ) * choose n k)= 1/(n+1) := by
  have l₁: ∑ k in range (n+1), ((-1:ℝ)^k)*(((1/(k+1)) : ℝ) * choose n k) =
   ∑ k in range (n+1), ((-1:ℝ)^k)*(((1/(n+1)) : ℝ) * choose (n+1) (k+1)):= by
    refine' sum_congr rfl fun k hk => _
    rw [choose_mul_eq_mul_sub_div]
  rw [l₁]
  have l₂:∑ k in range (n+1), ((-1:ℝ)^k)*(((1/(n+1)) : ℝ) * choose (n+1) (k+1)) =
    ∑ k in range (n+1), (((1/(n+1)) : ℝ) *(((-1:ℝ)^k)* choose (n+1) (k+1))) := by
    refine' sum_congr rfl fun k hk => _
    rw [← mul_assoc,← mul_assoc]
    congr 1
    rw [mul_comm]
  rw [l₂]
  rw[← mul_sum]
  have l₄ : ∑ k in range (n + 1), ((-1:ℝ)^k) * (choose (n+1) (k+1)) =
    ∑ k in range (n + 1), ((-1:ℝ)^k) * (choose n k + choose n (k+1)) := by
    refine' sum_congr rfl fun k hk => _
    rw [choose_succ_succ']
    congr 1
    rw [cast_add]
  have l₆: (1 / (↑n + 1):ℝ) =1 / (↑n + 1)*1 := by simp
  rw [l₆]
  rw [mul_assoc]
  congr 1
  simp
  have ne_one_neq_zero : (-1 :ℝ) ≠ 0 := by simp
  rw [← mul_right_inj' ne_one_neq_zero]
  rw [mul_sum]
  have l₅' :∑ x in range (n + 1), (-1 :ℝ) * ((-1) ^ x * ↑(Nat.choose (n + 1) (x + 1)))
   = ∑ x in range (n + 1), (-1 :ℝ) ^ (x+1) * ↑(Nat.choose (n + 1) (x + 1)) := by 
    refine' sum_congr rfl fun k hk => _
    rw [← mul_assoc,pow_add,mul_comm (-1) ((-1:ℝ) ^ k)]
    simp
  rw [l₅']
  have ne_mul_one: (-1 :ℝ)*1 = (-1 :ℝ) :=by simp
  rw [ne_mul_one]
  rw [range_eq_Ico]
  have sum_Ico_add_neone :∑ x in Ico 0 (n + 1), (-1:ℝ) ^ (x+1) * ↑(Nat.choose (n + 1) (x+1)) =
   ∑ x in Ico 1 (n + 2), (-1:ℝ) ^ (x) * ↑(Nat.choose (n + 1) (x)) := by
    rw [sum_Ico_add' fun x => (-1:ℝ) ^ x * Nat.choose (n + 1) x]
  rw [sum_Ico_add_neone]
  rw [← sum_Ico_sub_bot ]
  simp
  have n_add_two_eq_one_double : n+2 =n+1+1 := by simp
  rw [n_add_two_eq_one_double]
  have n_succ_neq_zero : n+1 ≠ 0 :=by simp
  rw [Rat.alternating_sum_range_choose_of_ne n_succ_neq_zero]
  linarith
