import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic

open Nat Finset BigOperators

theorem Idt31_a {n k : ℕ} : ascFactorial n k = descFactorial (n + k) k := by
  induction k
  · exact rfl
  · rename_i k H
    have h1 : ascFactorial n (succ k) = n.ascFactorial k.succ := by
      exact rfl
    have h2 : n.ascFactorial k.succ = (n + k + 1) * n.ascFactorial k := by
      exact h1
    have h3 : ascFactorial n (succ k) = (n + k + 1) * n.ascFactorial k := by
      exact h1
    have l1 : descFactorial (n + succ k) (succ k) = (n + k + 1) * descFactorial (n + k) k := by
      exact succ_descFactorial_succ (Nat.add n k) k
    exact Eq.symm (add_descFactorial_eq_ascFactorial n (succ k))
