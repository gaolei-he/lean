import Theorem.example_separate.choose_eq_pow_add

open Nat

open Finset

open BigOperators

theorem mul_sum_choose_sub_choose : (2 * n + 1) * ((∑ k in range (n+1), ((choose (2*n) k):ℝ)) - ((choose (2*n) n:ℝ))) = (2 * n + 1) * (2 ^ ( 2 * n - 1 ) - ((choose (2*n) n/ 2:ℝ))) := by
  rw[choose_eq_pow_add]
  congr 1
  rw[← add_sub]
  rw[div_two_sub_self]
  rw[← sub_eq_add_neg]


theorem mul_sum_choose_sub_choose_from_0_to_0(n : ℕ)(gol:  (2 * ↑n + 1) * (2 ^ (2 * n - 1) + ↑(Nat.choose (2 * n) n) / 2 - ↑(Nat.choose (2 * n) n)) =
    (2 * ↑n + 1) * (2 ^ (2 * n - 1) - ↑(Nat.choose (2 * n) n) / 2)) :
   (2 * ↑n + 1) * (∑ k in range (n + 1), ↑(Nat.choose (2 * n) k) - ↑(Nat.choose (2 * n) n)) =
    (2 * ↑n + 1) * (2 ^ (2 * n - 1) - ↑(Nat.choose (2 * n) n) / 2) := by
  rw[choose_eq_pow_add]
  apply gol

theorem mul_sum_choose_sub_choose_from_2_to_2(n : ℕ)(gol:  2 ^ (2 * n - 1) + (↑(Nat.choose (2 * n) n) / 2 - ↑(Nat.choose (2 * n) n)) =
    2 ^ (2 * n - 1) - ↑(Nat.choose (2 * n) n) / 2) :
   2 ^ (2 * n - 1) + ↑(Nat.choose (2 * n) n) / 2 - ↑(Nat.choose (2 * n) n) =
    2 ^ (2 * n - 1) - ↑(Nat.choose (2 * n) n) / 2 := by
  rw[← add_sub]
  apply gol

theorem mul_sum_choose_sub_choose_from_2_to_3(n : ℕ)(gol:  2 ^ (2 * n - 1) + -(↑(Nat.choose (2 * n) n) / 2) = 2 ^ (2 * n - 1) - ↑(Nat.choose (2 * n) n) / 2) :
   2 ^ (2 * n - 1) + ↑(Nat.choose (2 * n) n) / 2 - ↑(Nat.choose (2 * n) n) =
    2 ^ (2 * n - 1) - ↑(Nat.choose (2 * n) n) / 2 := by
  rw[← add_sub]
  rw[div_two_sub_self]
  apply gol

theorem mul_sum_choose_sub_choose_from_2_to_4(n : ℕ) :
   2 ^ (2 * n - 1) + ↑(Nat.choose (2 * n) n) / 2 - ↑(Nat.choose (2 * n) n) =
    2 ^ (2 * n - 1) - ↑(Nat.choose (2 * n) n) / 2 := by
  rw[← add_sub]
  rw[div_two_sub_self]
  rw[← sub_eq_add_neg]

theorem mul_sum_choose_sub_choose_from_3_to_3(n : ℕ)(gol:  2 ^ (2 * n - 1) + -(↑(Nat.choose (2 * n) n) / 2) = 2 ^ (2 * n - 1) - ↑(Nat.choose (2 * n) n) / 2) :
   2 ^ (2 * n - 1) + (↑(Nat.choose (2 * n) n) / 2 - ↑(Nat.choose (2 * n) n)) =
    2 ^ (2 * n - 1) - ↑(Nat.choose (2 * n) n) / 2 := by
  rw[div_two_sub_self]
  apply gol

theorem mul_sum_choose_sub_choose_from_3_to_4(n : ℕ) :
   2 ^ (2 * n - 1) + (↑(Nat.choose (2 * n) n) / 2 - ↑(Nat.choose (2 * n) n)) =
    2 ^ (2 * n - 1) - ↑(Nat.choose (2 * n) n) / 2 := by
  rw[div_two_sub_self]
  rw[← sub_eq_add_neg]

theorem mul_sum_choose_sub_choose_from_4_to_4(n : ℕ) :
   2 ^ (2 * n - 1) + -(↑(Nat.choose (2 * n) n) / 2) = 2 ^ (2 * n - 1) - ↑(Nat.choose (2 * n) n) / 2 := by
  rw[← sub_eq_add_neg]

