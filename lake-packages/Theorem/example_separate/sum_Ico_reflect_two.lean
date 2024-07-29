import Theorem.example_separate.prod_Ico_reflect_two


open Finset

open BigOperators


theorem sum_Ico_reflect_two {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
    (h : m ≤ 2 * n + 1) : (∑ j in Ico k m, f (2 * n - j)) = ∑ j in Ico (2 * n + 1 - m) (2 * n + 1 - k), f j :=
  @prod_Ico_reflect_two (Multiplicative δ) _ f k m n h
