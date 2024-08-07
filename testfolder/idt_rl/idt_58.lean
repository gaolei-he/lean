import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl
open Nat Finset BigOperators


theorem Idt_58 {n m : ℕ} : ∑ k in range (n+1), choose k m = choose (n+1) (m+1) := by lean_repl sorry
  induction n
  . exact rfl
  . rename_i n h₁
    rw [sum_range_succ, choose_succ_succ', h₁, add_comm]
