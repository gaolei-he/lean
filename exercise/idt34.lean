import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic

open Nat Finset BigOperators

theorem Idt31 {n k : ℕ} : ascFactorial n k = descFactorial (n + k - 1 + 1) k := by
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

theorem Idt33 {n k x y: ℕ} : ∑ k in range (n + 1), (choose n k) * (descFactorial (x + 1) k) * (descFactorial (y + 1) (n - k)) = descFactorial (x + y + 1) n := by
  sorry

theorem Idt34 {n k x y : ℕ}{hx: 1 ≤ x}{hy: 1 ≤ y} : ∑ k in range (n + 1), (choose n k) * (ascFactorial x k) * (ascFactorial y (n - k)) = ascFactorial (x + y) n := by
  have h_left:  ∑ k in range (n + 1), (choose n k) * (ascFactorial x k) * (ascFactorial y (n - k)) =  ∑ k in range (n + 1), (choose n k) * (descFactorial (x + k  - 1 + 1) k) * (descFactorial (y + (n - k) - 1 + 1) (n - k)) := by
    refine' sum_congr rfl fun y hy => _
    rw[Idt31, Idt31]
  have h_right: ascFactorial (x + y) n = descFactorial ((x + y) + n) n := by
    rw[Idt31]
    rw[Nat.sub_add_cancel]
    have h0: 1 ≤ x + y + n := by linarith
    exact h0
  rw[h_left, h_right]
  have h_d: descFactorial (x + y + n) n = descFactorial (x + (y + n) - 1 + 1) n := by
    rw[add_assoc]
    rw[Nat.sub_add_cancel]
    have h1: 1 ≤ x + (y + n) := by linarith
    exact h1
  have h_d' :descFactorial (x + y + n) n = descFactorial (x + (y + n - 1) + 1) n := by
    rw[h_d]
    rw[Nat.add_sub_assoc]
    have h2: 1 ≤ (y + n) := by linarith
    exact h2
  rw[h_d']
  rw[← Idt33]
  refine' sum_congr rfl fun y hy => _
  sorry
