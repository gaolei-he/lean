import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem add_div_two_eq_distrib(hn : n ≠ 0) :
 (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 =
  2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by
   rw[add_div_two hn]


theorem add_div_two_eq_distrib_from_0_to_0(n : ℕ)(hn : n ≠ 0) :
   (Nat.choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  rw[add_div_two hn]

