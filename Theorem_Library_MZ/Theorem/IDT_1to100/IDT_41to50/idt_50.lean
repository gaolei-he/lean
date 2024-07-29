import Mathlib.Data.Nat.Choose.Sum
import Theorem.IDT_1to100.IDT_1to10.idt_3


open Nat
open Finset
open BigOperators


theorem idt50 { m n k : ℕ } (hnk: k <= n) (hkm : m <=k) (h : Commute x y): ∑k in range (n+1),(n.choose k)*(k.choose m)*x^(n-k)*y^(k-m) =
  (x+y)^(n-m) * choose n m := by
  have h1: n+1 =  m + (n - m +1) := by
    rw [add_comm m]
    rw [add_assoc]
    rw [add_comm 1]
    rw [←add_assoc]
    rw [tsub_add_cancel_of_le]
    exact Nat.le_trans hkm hnk
  rw [h1]
  rw [sum_range_add]
  have h2: ∑ a in range m,(Nat.choose n a) * (Nat.choose a m) * x ^ (n - a) * y ^ (a - m) = 0 :=by
    rw [sum_congr rfl fun a ha => by
      let ha1 := mem_range.mp ha
      rw [choose_eq_zero_of_lt ha1]
    ]
    simp [sum_const_zero]
  rw [h2, zero_add]
  rw [add_comm x y]
  rw [idt3_Binomial (Commute.symm h)]
  rw [sum_mul]
  apply sum_congr rfl
  intro a ha
  rw [add_comm m a,add_tsub_cancel_right]
  repeat rw [←mul_assoc]
  rw [mul_comm]
  repeat rw [mul_assoc]
  congr 1
  have h3: x ^ (n - (a + m)) = x ^ (n - m - a) := by
    congr 1
    rw [tsub_add_eq_tsub_tsub]
    exact Nat.sub_right_comm n a m
  rw [h3]
  symm
  repeat rw [← mul_assoc]
  rw [mul_assoc,mul_comm]
  congr 1
  let hamn: a + m <= n := by
    apply le_of_lt_succ
    rw [succ_eq_add_one]
    linarith [mem_range.mp ha]
  let hma: m <= a + m := by
    rw [add_comm]
    exact le_add_right m a
  simp [Nat.choose_mul hamn hma]
  rw [mul_comm]
