import Theorem.example_separate.add_div_two

open Finset

open BigOperators

theorem sum_neg_cancel(hn : 1 < n) : ∑ x in range n, (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) = ∑ x in range (n - 1 + 1), (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) := by
  have zero_lt_n : 0 < n := by linarith
  rw[Nat.sub_add_cancel zero_lt_n]
