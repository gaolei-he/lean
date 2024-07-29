import Theorem.example_separate.choose_le_sum
import Theorem.example_separate.range_sub_choose_add_sum

open Nat

open Finset

open BigOperators


theorem sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   -- an + an = 2 ^ ( 2 * n ) + choose (2 * n) n
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by
      rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
      simp
      rw [Nat.sub_add_cancel choose_le_sum]
  rw[←sum_sub_sum_add,sum_add_eq_add]


theorem sum_add_eq_two_pow_from_0_to_0(n : ℕ)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =
    2 ^ (2 * n) + Nat.choose (2 * n) n) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =
    2 ^ (2 * n) + Nat.choose (2 * n) n := by
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  apply gol

theorem sum_add_eq_two_pow_from_0_to_1(n : ℕ)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =
    2 ^ (2 * n) + Nat.choose (2 * n) n) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =
    2 ^ (2 * n) + Nat.choose (2 * n) n := by
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by
      rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
      simp
      rw [Nat.sub_add_cancel choose_le_sum]
  apply gol

theorem sum_add_eq_two_pow_from_0_to_2(n : ℕ) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =
    2 ^ (2 * n) + Nat.choose (2 * n) n := by
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by
      rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
      simp
      rw [Nat.sub_add_cancel choose_le_sum]
  rw[←sum_sub_sum_add,sum_add_eq_add]

theorem sum_add_eq_two_pow_from_1_to_1(n : ℕ)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =
    2 ^ (2 * n) + Nat.choose (2 * n) n) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =
    2 ^ (2 * n) + Nat.choose (2 * n) n := by
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by
      rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
      simp
      rw [Nat.sub_add_cancel choose_le_sum]
  apply gol

theorem sum_add_eq_two_pow_from_1_to_2(n : ℕ)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =
    2 ^ (2 * n) + Nat.choose (2 * n) n := by
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by
      rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
      simp
      rw [Nat.sub_add_cancel choose_le_sum]
  rw[←sum_sub_sum_add,sum_add_eq_add]

theorem sum_add_eq_two_pow_from_2_to_2(n : ℕ)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =
    2 ^ (2 * n) + Nat.choose (2 * n) n := by
  rw[←sum_sub_sum_add,sum_add_eq_add]

