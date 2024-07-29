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


theorem sum_eq_mul_mul_add_pow_from_0_to_0(n : ℕ)(h : 2 ≤ n)(gol:  ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1))) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1)) := by
  have h0: 0 < n:= by linarith
  apply gol

theorem sum_eq_mul_mul_add_pow_from_0_to_1(n : ℕ)(h : 2 ≤ n)(gol:  n * ∑ k in Ico 1 (n + 1), k * Nat.choose (n - 1) (k - 1) = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1))) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1)) := by
  have h0: 0 < n:= by linarith
  rw[Ico_pow_mul_choose]
  apply gol

theorem sum_eq_mul_mul_add_pow_from_0_to_2(n : ℕ)(h : 2 ≤ n)(gol:  n * (∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1))) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1)) := by
  have h0: 0 < n:= by linarith
  rw[Ico_pow_mul_choose]
  rw[Ico_choose_eq_Ico_choose_add h0]
  apply gol

theorem sum_eq_mul_mul_add_pow_from_0_to_3(n : ℕ)(h : 2 ≤ n) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1)) := by
  have h0: 0 < n:= by linarith
  rw[Ico_pow_mul_choose]
  rw[Ico_choose_eq_Ico_choose_add h0]
  rw[Ico_choose_add_eq_mul_pred h0,pred_Ico_choose, pred_Ico_choose_eq_pred_pow h]

theorem sum_eq_mul_mul_add_pow_from_1_to_1(n : ℕ)(h : 2 ≤ n)(h0 : 0 < n)(gol:  n * ∑ k in Ico 1 (n + 1), k * Nat.choose (n - 1) (k - 1) = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1))) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1)) := by
  rw[Ico_pow_mul_choose]
  apply gol

theorem sum_eq_mul_mul_add_pow_from_1_to_2(n : ℕ)(h : 2 ≤ n)(h0 : 0 < n)(gol:  n * (∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1))) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1)) := by
  rw[Ico_pow_mul_choose]
  rw[Ico_choose_eq_Ico_choose_add h0]
  apply gol

theorem sum_eq_mul_mul_add_pow_from_1_to_3(n : ℕ)(h : 2 ≤ n)(h0 : 0 < n) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1)) := by
  rw[Ico_pow_mul_choose]
  rw[Ico_choose_eq_Ico_choose_add h0]
  rw[Ico_choose_add_eq_mul_pred h0,pred_Ico_choose, pred_Ico_choose_eq_pred_pow h]

theorem sum_eq_mul_mul_add_pow_from_2_to_2(n : ℕ)(h : 2 ≤ n)(h0 : 0 < n)(gol:  n * (∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1))) :
   n * ∑ k in Ico 1 (n + 1), k * Nat.choose (n - 1) (k - 1) = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1)) := by
  rw[Ico_choose_eq_Ico_choose_add h0]
  apply gol

theorem sum_eq_mul_mul_add_pow_from_2_to_3(n : ℕ)(h : 2 ≤ n)(h0 : 0 < n) :
   n * ∑ k in Ico 1 (n + 1), k * Nat.choose (n - 1) (k - 1) = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1)) := by
  rw[Ico_choose_eq_Ico_choose_add h0]
  rw[Ico_choose_add_eq_mul_pred h0,pred_Ico_choose, pred_Ico_choose_eq_pred_pow h]

theorem sum_eq_mul_mul_add_pow_from_3_to_3(n : ℕ)(h : 2 ≤ n)(h0 : 0 < n) :
   n * (∑ l in Ico 1 n, l * Nat.choose (n - 1) l + 2 ^ (n - 1)) = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1)) := by
  rw[Ico_choose_add_eq_mul_pred h0,pred_Ico_choose, pred_Ico_choose_eq_pred_pow h]

