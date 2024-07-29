import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub_div

open Nat
open Finset
open BigOperators


theorem idt24 {n k: ℕ}:
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
  have l₄ : ∑ k in range (n + 1), ((-1:ℝ)^k) * (choose (n+1) (k+1)) = 1 := by sorry
    -- rw [choose_succ_succ']
  rw [l₄]
  simp
