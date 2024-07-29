import Mathlib.Data.Nat.Choose.Sum
open Nat
open Finset
open BigOperators


theorem idt1_Pascal's_Recurrence(h1:1 ≤ n)(h2:1 ≤ k) : choose n k = choose (n-1) k  + choose (n-1) (k-1) := by
  have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]


theorem Idt20 {n k : ℕ} {h1 : n >=1 } : ∑ k in range (m +1), (choose n k) * (-1:ℤ)^k = (-1:ℤ)^m * choose (n -1) m := by
  induction' m with d hd
  · simp
  · rw [sum_range_succ]
    rw [hd]
    rw [pow_succ (-1:ℤ) d]
    simp [← mul_assoc]
    rw [mul_comm]
    rw [neg_mul_eq_neg_mul]
    rw [← add_mul]
    rw [mul_comm ((-1:ℤ)^d) _]
    rw [neg_mul_eq_neg_mul]
    rw [mul_comm]
    rw [mul_comm _ ((-1:ℤ)^d)]
    apply congr_arg
    rw [succ_eq_add_one]

    apply add_neg_eq_of_eq_add
    rw [neg_add_eq_sub]
    symm
    apply sub_eq_of_eq_add

    rw [idt1_Pascal's_Recurrence h1]
    rw [add_comm]
    simp [add_sub_cancel]
    simp [mul_add]
