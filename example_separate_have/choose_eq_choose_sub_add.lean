import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem choose_eq_choose_sub_add(h1:1 ≤ n)(h2:1 ≤ k) :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
