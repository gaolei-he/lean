import Mathlib.Data.Nat.Choose.Sum
import Theorem.IDT_1to100.IDT_1to10.idt_1
import Lean4Repl

open Nat

open Finset

open BigOperators


theorem Idt15 {m n : ℕ} :
  (∑ k in range (m + 1), choose (n + k) k) = choose (n + m + 2) m := by lean_repl sorry
   induction m
   · have h1 : ∀ a : ℕ , choose a 0 = 1 := by
      exact fun a => choose_zero_right a
     exact h1 (n + 0)
   · rename_i m IH
     have c1 : ∑ k in range (succ m + 1), choose (n + k) k = choose (n + succ m + 2) (succ m) := by
        have h2 : ∑ k in range (succ m + 1), choose (n + k) k = ∑ k in range (m + 2), choose (n + k) k := by
          have l1 : (succ m + 1) = m + 2 := by
            exact rfl
          have l2 : ∑ k in range (succ m + 1), choose (n + k) k = ∑ k in range (m + 2), choose (n + k) k := by
            exact rfl
          exact l2
        have h3 : choose (n + succ m + 2) (succ m) = choose (n + m + 3) (m + 1) := by
          have l3 : (n + succ m + 2) = n + m + 3 := by
            exact rfl
          have l4 : succ m = m + 1 := by
            exact rfl
          exact rfl
        have h4 : ∑ k in range (m + 2), choose (n + k) k = choose (n + m + 3) (m + 1) := by
          have e1 : ∑ k in range (m + 2), choose (n + k) k = (∑ k in range (m + 1), choose (n + k) k) + choose (n + m + 2) (m + 1) := by
            sorry
          have e2 : ∑ k in range (m + 2), choose (n + k) k = choose (n + m + 2) m +choose (n + m + 2) (m + 1) := by
            rw[e1]
            exact congrFun (congrArg HAdd.hAdd IH) (Nat.choose (n + m + 2) (m + 1))
          have e3 : choose (n + m + 2) m +choose (n + m + 2) (m + 1) = choose (n + m + 3) (m + 1) := by
            exact h3
          exact e2
        exact h4
     exact c1
