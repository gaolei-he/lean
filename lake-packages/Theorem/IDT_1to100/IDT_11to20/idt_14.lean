import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Theorem.Lemma.sum_parity
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Basic

open Nat
open Finset
open BigOperators




theorem Idt14 {n : ℕ}: ∑ k in filter Odd (range (n + 1)), Nat.choose n k = 2 ^(n-1) *(if 1 ≤ n then 1 else 0) :=by

  have h1: ∑ k in filter Odd (range (n + 1)), Nat.choose n k = sum_choose_odd n :=by
    simp [sum_filter]
    rw [sum_choose_odd]
    simp

  rw [h1]
  rw [sum_choose_odd_eval]
