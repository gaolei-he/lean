import Mathlib.Data.Nat.Choose.Sum
import Theorem.IDT_1to100.IDT_1to10.idt_1


open Nat
open Finset
open BigOperators



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
