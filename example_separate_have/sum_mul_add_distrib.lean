import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem sum_mul_add_distrib : ∑ k in range (n+1), (k+1) * choose n k = ∑ k in range (n+1), (k * choose n k + 1 * choose n k) := by
  refine' sum_congr rfl fun y _ => _
  rw[add_mul]
