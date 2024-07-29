import Mathlib.Data.Nat.Choose.Sum
import Theorem.IDT_1to100.IDT_1to10.idt_6

open Nat
open Finset
open BigOperators

theorem idt_35 (n : ℕ)(hn2 : 2 ≤ n): ∑ k in range (n + 1), (choose n k) *k*(k-1) = n*(n-1)*2^(n-2):= by
 rw[range_eq_Ico]
 have hn0: 0 < n  := by linarith
 have h_succ : 0 < n + 1 := by linarith
 have Ico_choose_simp: ∑ k in Ico 0 (n + 1), (choose n k) *k*(k-1) =
  ∑ k in Ico 1 (n + 1), (choose n k) *k*(k-1) := by
    rw [sum_eq_sum_Ico_succ_bot h_succ]
    simp
 rw [Ico_choose_simp]
 have Ico_choose_ntok:∑ k in Ico 1 (n + 1), (choose n k) *k*(k-1) =
  ∑ k in Ico 1 (n + 1), n * ((k - 1) * Nat.choose (n - 1) (k - 1)):= by
   refine' sum_congr rfl fun x hx ↦ _
   have hx_succ: x < n + 1 := by exact (mem_Ico.1 hx).2
   have hxn : x ≤ n := by linarith
   have hx1 : 1 ≤ x := by exact (mem_Ico.1 hx).1
   rw [mul_comm (choose n x) x,mul_comm]
   rw [idt6_Absorption (hxn) (hx1),← mul_assoc,mul_comm (x-1) n ,mul_assoc]
 rw [Ico_choose_ntok]
 rw[sum_Ico_eq_sum_range]
 simp
 rw[range_eq_Ico]
 rw [← mul_sum]
 rw [mul_assoc]
 congr 1
 rw [sum_eq_sum_Ico_succ_bot hn0]
 simp
 have Ico_choose_simp: ∑ x in Ico 1 n, x * Nat.choose (n - 1) x =
  ∑ x in Ico 1 n, (n-1) * Nat.choose (n - 2) (x-1) := by
    refine' sum_congr rfl fun y hy ↦ _
    have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hyn : y < n := by exact (mem_Ico.1 hy).2
    have hyn_sub_one : y ≤ n-1 := by
     rw [← Nat.lt_iff_le_pred hn0]
     linarith
    rw [idt6_Absorption hyn_sub_one hy1]
    congr 1
 rw [Ico_choose_simp]
 rw [← mul_sum]
 rw[sum_Ico_eq_sum_range]
 congr 1
 simp
 have sub_two_add_one_simp : n - 2 + 1 = n-1 := by exact tsub_add_eq_add_tsub hn2
 have two_to_one_add_one:2 ^ (n - 2) =(1+1) ^ (n-2) := by simp
 rw [two_to_one_add_one]
 rw [add_pow 1 1 (n-2)]
 norm_num
 rw [sub_two_add_one_simp]
