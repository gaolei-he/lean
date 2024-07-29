import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub_div

open Nat
open Finset
open BigOperators


theorem choose_mul_eq_mul_sub_div2 {n: ℕ} :
 ∑ k in range (n+1),(choose n k) *(1/(k + 1:ℝ)) =
    ∑ k in range (n+1),(1/(n+1:ℝ)) *(choose (n+1) (k+1)) := by
      refine' sum_congr rfl fun k hk ↦ _
      have l₁: (k + 1 :ℝ)≠ 0 := by linarith
      have l₂: (n + 1:ℝ) ≠ 0 := by linarith
      have l₁': (1 :ℝ)≠ 0 := by linarith
      apply mul_right_cancel₀ l₁
      apply mul_left_cancel₀ l₂
      rw [mul_assoc,mul_comm,div_mul,div_self l₁,div_self l₁',mul_assoc,one_mul]
      rw [mul_assoc,← mul_assoc]
      rw [mul_one_div (n + 1:ℝ) (n + 1:ℝ),div_self l₂,one_mul]
      rw [mul_comm,← cast_one,← cast_add,← cast_mul,← cast_add,← cast_mul]
      have h2 : (n + 1) * Nat.choose n k= (succ n) * Nat.choose n k := by
         rw [succ_eq_add_one]
      rw [h2]
      have h3 :Nat.choose (n + 1) (k + 1) * (k + 1) =Nat.choose (n + 1) (k + 1) * (succ k) :=
       by rw [succ_eq_add_one]
      rw [h3]
      rw [succ_mul_choose_eq]
