import Theorem.example_separate.choose_mul_eq_mul_sub_div


open Nat

open Finset

open BigOperators

theorem neg_pow_mul_div_mul: ∑ k in range (n+1), ((-1 : ℝ) ^ k) * (1 / ((k + 1)) : ℝ ) * ((1 / ((k + 1)) : ℝ )) * choose n k = ∑ k in range (n+1), (1/(n+1)) * (((-1 : ℝ) ^ k) * (1 / ((k + 1)) : ℝ ) * choose (n+1) (k+1)) := by
    refine' sum_congr rfl fun y hy => _
    rw[mul_assoc, choose_mul_eq_mul_sub_div, ← mul_assoc]
    rw[mul_comm ((-1 : ℝ) ^ y * (1 / (↑y + 1))) (1 / (n + 1))]
    rw[← mul_assoc]
    rw[mul_assoc, mul_assoc,mul_assoc]
