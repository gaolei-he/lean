import Theorem.example_separate.Ico_choose_add_eq_mul_pred
import Theorem.example_separate.Ico_pow_mul_choose
import Theorem.example_separate.Ico_choose_eq_Ico_choose_add
import Theorem.example_separate.pred_Ico_choose
import Theorem.example_separate.pred_Ico_choose_eq_pred_pow

open Nat

open Finset

open BigOperators


theorem sum_eq_mul_mul_add_pow(h: 2 ≤ n) : ∑ k in Ico 1 (n + 1), k ^ 2 * choose n k = n *((n - 1) * 2 ^ (n-2)  + 2 ^ ( n - 1 )) := by
    have h0: 0 < n:= by linarith
    rw[Ico_pow_mul_choose]
    rw[Ico_choose_eq_Ico_choose_add h0]
    rw[Ico_choose_add_eq_mul_pred h0,pred_Ico_choose, pred_Ico_choose_eq_pred_pow h]
