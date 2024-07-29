import Theorem.example_separate.sum_eq_two

open Nat

open Finset

open BigOperators

theorem two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]


theorem two_pow_eq_range_add_ico_from_0_to_0(n : ℕ) :
   2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k := by
  rw[ ← sum_eq_two ]

