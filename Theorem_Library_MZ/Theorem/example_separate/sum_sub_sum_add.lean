import Theorem.example_separate.choose_le_sum

open Nat

open Finset

open BigOperators


theorem sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by
    rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]


theorem sum_sub_sum_add_from_0_to_0(n : ℕ)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + Nat.choose (2 * n) n +
      ∑ k in range (n + 1), Nat.choose (2 * n) k =
    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +
      Nat.choose (2 * n) n =
    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k := by
  rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
  apply gol

theorem sum_sub_sum_add_from_0_to_1(n : ℕ)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + Nat.choose (2 * n) n =
    ∑ k in range (n + 1), Nat.choose (2 * n) k) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +
      Nat.choose (2 * n) n =
    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k := by
  rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
  simp
  apply gol

theorem sum_sub_sum_add_from_0_to_2(n : ℕ) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +
      Nat.choose (2 * n) n =
    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k := by
  rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
  simp
  rw [Nat.sub_add_cancel choose_le_sum]

theorem sum_sub_sum_add_from_1_to_1(n : ℕ)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + Nat.choose (2 * n) n =
    ∑ k in range (n + 1), Nat.choose (2 * n) k) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + Nat.choose (2 * n) n +
      ∑ k in range (n + 1), Nat.choose (2 * n) k =
    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k := by
  simp
  apply gol

theorem sum_sub_sum_add_from_1_to_2(n : ℕ) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + Nat.choose (2 * n) n +
      ∑ k in range (n + 1), Nat.choose (2 * n) k =
    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k := by
  simp
  rw [Nat.sub_add_cancel choose_le_sum]

theorem sum_sub_sum_add_from_2_to_2(n : ℕ) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + Nat.choose (2 * n) n =
    ∑ k in range (n + 1), Nat.choose (2 * n) k := by
  rw [Nat.sub_add_cancel choose_le_sum]

