import Mathlib.Data.Nat.Choose.Sum

open Nat Finset BigOperators

theorem Idt_59 {n : ℕ} : ∑ k in range (n+1), k = choose (n+1) 2 := by
  induction n
  . exact rfl
  . rename_i n h₁
    rw [sum_range_succ, choose_succ_succ', h₁, ←one_add_one_eq_two, add_comm]
    simp
