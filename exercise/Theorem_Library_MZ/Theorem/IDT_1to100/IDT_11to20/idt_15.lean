import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem idt1_Pascal's_Recurrence(h1:1 ≤ n)(h2:1 ≤ k) : choose n k = choose (n-1) k  + choose (n-1) (k-1) := by
  have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]

theorem Idt15 {m n : ℕ} :
  (∑ k in range (m + 1), choose (n + k) k) = choose (n + m + 2) m := by
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
