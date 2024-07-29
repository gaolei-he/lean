import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Theorem.IDT_1to100.IDT_1to10.idt_1
import Lean4Repl

open Nat

theorem idt8 {n k : ℕ} (hk : k ≤ n) (hk1 :1 ≤ k):
 (n-k)*choose n k = n * choose (n-1) k  := by  lean_repl sorry
  have h₁:1 ≤ n := by linarith
  rw [idt1_Pascal's_Recurrence h₁ hk1]
  rw [mul_add]
  have h₂ :(n - k)  =((n-1)- (k-1)) := by
    rw [tsub_tsub_tsub_cancel_right]
    linarith
  rw [h₂,mul_comm (n - 1 - (k - 1)) (choose (n - 1) (k - 1)),← choose_succ_right_eq (n-1) (k-1)]
  rw [Nat.sub_add_cancel hk1]
  rw [← h₂]
  rw [tsub_mul]
  rw [mul_comm (choose (n - 1) k)]
  rw [tsub_add_cancel_of_le]
  exact Nat.mul_le_mul_right _ hk
