import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem sum_neg_pow_mul_mul_choose : ∑ k in range (n+1), (-1 : ℤ)^k * k * (choose n k)  = (-1 : ℤ)^0 * 0 * (choose n 0) + ∑ k in Ico 1 (n+1), (-1 : ℤ)^k * k * (choose n k) := by
    rw[range_eq_Ico]
    have n_succ: 0 < n + 1 := by linarith
    rw[sum_eq_sum_Ico_succ_bot n_succ]
    simp
