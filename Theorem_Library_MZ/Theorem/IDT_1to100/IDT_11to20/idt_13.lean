import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Parity
import Theorem.Lemma.sum_parity

open Nat

open Finset

open BigOperators



theorem Idt13 {n : ℕ}: ∑ k in filter Even (range (n + 1)), Nat.choose n k = 2 ^(n-1) + (1/2) *(1/2)*(if 1 ≤ n then 1 else 0) :=by

  have h1: ∑ k in filter Even (range (n + 1)), Nat.choose n k = sum_choose_even n :=by
    simp [sum_filter]
    rw [sum_choose_even]

  rw [h1]
  rw [sum_choose_even_eval]
  rfl
