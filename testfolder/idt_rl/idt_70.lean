import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Theorem.IDT_1to100.IDT_1to10.idt_1

open Nat
open Finset
open BigOperators




theorem idt70 {n k:ℕ}(hn:1 ≤ n)(hk:1 ≤ k) : multichoose n k = multichoose n (k-1) + multichoose (n-1) k :=by
  simp [multichoose_eq]
  ring_nf
  let h1: 1 ≤ (n + k-1) :=by
    rw [Nat.add_sub_assoc]
    nth_rw 1 [←zero_add 1]
    rw [add_comm]

    apply Nat.add_le_add
    exact hn
    exact Nat.zero_le (k-1)
    exact hk
  rw [idt1_Pascal's_Recurrence h1 hk]
  rw [add_comm]
  ring_nf
  congr 1
  {
    congr 2
    symm
    rw [Nat.add_sub_assoc hk]
  }
  {
    congr 1
    congr 1
    rw [add_comm]
    rw [Nat.add_sub_assoc hn]
  }
