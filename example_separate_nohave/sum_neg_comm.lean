import Theorem.example_separate.add_div_two


open Finset

open BigOperators

theorem sum_neg_comm : ∑ x in range n, (-1 : ℤ) ^ x * n * ↑(Nat.choose (n - 1) x) =  ∑ x in range n, n * (-1 : ℤ) ^ x * ↑(Nat.choose (n - 1) x):= by
    refine' sum_congr rfl fun y _ => _
    congr 1
    rw[mul_comm]
