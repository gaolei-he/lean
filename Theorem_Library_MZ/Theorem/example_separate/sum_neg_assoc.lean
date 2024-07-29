import Theorem.example_separate.add_div_two


open Finset

open BigOperators


theorem sum_neg_assoc: ∑ x in range n, n * (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x) =  ∑ x in range n, n * ((-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x)) := by
  refine' sum_congr rfl fun y _ => _
  rw[mul_assoc]


theorem sum_neg_assoc_from_1_to_1(n y : ℕ)(x✝ : y ∈ range n) :
   ↑n * (-1 : ℝ) ^ y * ↑(Nat.choose (n - 1) y) = ↑n * ((-1 : ℝ) ^ y * ↑(Nat.choose (n - 1) y)) := by
  rw[mul_assoc]

