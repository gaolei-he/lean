import Theorem.example_separate.add_div_two
import Lean4Repl
open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem sum_neg_pow_mul_mul_choose : ∑ k in range (n+1), (-1 : ℤ)^k * k * (choose n k)  = (-1 : ℤ)^0 * 0 * (choose n 0) + ∑ k in Ico 1 (n+1), (-1 : ℤ)^k * k * (choose n k) := by lean_repl sorry
    rw[range_eq_Ico]
    rw[sum_eq_sum_Ico_succ_bot]
    simp
    linarith
