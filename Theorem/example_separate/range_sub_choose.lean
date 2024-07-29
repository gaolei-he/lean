import Theorem.example_separate.Ico_choose_range_choose

open Nat

open Finset

open BigOperators



theorem range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]


theorem range_sub_choose_from_0_to_0(n : ℕ) :
   ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =
    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n := by
  rw[Ico_choose_range_choose]

