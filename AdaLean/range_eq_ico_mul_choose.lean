import AdaLean.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators


theorem range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by
  rw[range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot]
  simp
  linarith
