import Theorem.example_separate.choose_le_sum

open Nat

open Finset

open BigOperators


theorem sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by
    rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
