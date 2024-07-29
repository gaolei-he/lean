import Theorem.example_separate.Ico_choose_add_eq_mul_pred
import Theorem.example_separate.Ico_pow_mul_choose
import Theorem.example_separate.Ico_choose_eq_Ico_choose_add
import Theorem.example_separate.pred_Ico_choose
import Theorem.example_separate.pred_Ico_choose_eq_pred_pow
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999

theorem sum_eq_mul_mul_add_pow(h: 2 ≤ n) : ∑ k in Ico 1 (n + 1), k ^ 2 * choose n k = n *((n - 1) * 2 ^ (n-2)  + 2 ^ ( n - 1 )) := by lean_repl sorry
    rw[Ico_pow_mul_choose]
    rw[Ico_choose_eq_Ico_choose_add]
    rw[Ico_choose_add_eq_mul_pred,pred_Ico_choose, pred_Ico_choose_eq_pred_pow h]
    linarith
    linarith
