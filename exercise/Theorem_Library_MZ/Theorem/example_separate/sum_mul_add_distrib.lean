import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem sum_mul_add_distrib : ∑ k in range (n+1), (k+1) * choose n k = ∑ k in range (n+1), (k * choose n k + 1 * choose n k) := by
  refine' sum_congr rfl fun y _ => _
  rw[add_mul]


theorem sum_mul_add_distrib_from_1_to_1(n y : ℕ)(x✝ : y ∈ range (n + 1)) :
   (y + 1) * Nat.choose n y = y * Nat.choose n y + 1 * Nat.choose n y := by
  rw[add_mul]

