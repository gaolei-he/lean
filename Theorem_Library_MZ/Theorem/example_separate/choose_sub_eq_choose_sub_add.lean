import Theorem.example_separate.add_div_two

open Nat

theorem choose_sub_eq_choose_sub_add(h1:1 ≤ n)(h2:1 ≤ k) :
 choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]


theorem choose_sub_eq_choose_sub_add_from_0_to_0(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k) :
   choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by
  rw[Nat.sub_add_cancel h2]

