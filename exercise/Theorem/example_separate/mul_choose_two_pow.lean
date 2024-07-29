import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem mul_choose_two_pow(hn : 0 < n) : n * ∑ l in range n, choose (n-1) l = n * 2 ^ (n-1) := by
  congr 1
  have n1 : 1 ≤ n := by linarith
  have hn1 : ∑ l in range n, choose (n-1) l = ∑ l in range (n - 1 + 1), choose (n-1) l   := by
    rw[Nat.sub_add_cancel n1]
  rw[hn1]
  rw [sum_range_choose]


theorem mul_choose_two_pow_from_1_to_1(n : ℕ)(hn : 0 < n)(gol:  ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have n1 : 1 ≤ n := by linarith
  apply gol

theorem mul_choose_two_pow_from_1_to_2(n : ℕ)(hn : 0 < n)(gol:  ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have n1 : 1 ≤ n := by linarith
  have hn1 : ∑ l in range n, choose (n-1) l = ∑ l in range (n - 1 + 1), choose (n-1) l   := by
    rw[Nat.sub_add_cancel n1]
  apply gol

theorem mul_choose_two_pow_from_1_to_3(n : ℕ)(hn : 0 < n)(gol:  ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have n1 : 1 ≤ n := by linarith
  have hn1 : ∑ l in range n, choose (n-1) l = ∑ l in range (n - 1 + 1), choose (n-1) l   := by
    rw[Nat.sub_add_cancel n1]
  rw[hn1]
  apply gol

theorem mul_choose_two_pow_from_1_to_4(n : ℕ)(hn : 0 < n) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have n1 : 1 ≤ n := by linarith
  have hn1 : ∑ l in range n, choose (n-1) l = ∑ l in range (n - 1 + 1), choose (n-1) l   := by
    rw[Nat.sub_add_cancel n1]
  rw[hn1]
  rw [sum_range_choose]

theorem mul_choose_two_pow_from_2_to_2(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n)(gol:  ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have hn1 : ∑ l in range n, choose (n-1) l = ∑ l in range (n - 1 + 1), choose (n-1) l   := by
    rw[Nat.sub_add_cancel n1]
  apply gol

theorem mul_choose_two_pow_from_2_to_3(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n)(gol:  ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have hn1 : ∑ l in range n, choose (n-1) l = ∑ l in range (n - 1 + 1), choose (n-1) l   := by
    rw[Nat.sub_add_cancel n1]
  rw[hn1]
  apply gol

theorem mul_choose_two_pow_from_2_to_4(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  have hn1 : ∑ l in range n, choose (n-1) l = ∑ l in range (n - 1 + 1), choose (n-1) l   := by
    rw[Nat.sub_add_cancel n1]
  rw[hn1]
  rw [sum_range_choose]

theorem mul_choose_two_pow_from_3_to_3(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n)(hn1 : ∑ l in range n, Nat.choose (n - 1) l = ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l)(gol:  ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l = 2 ^ (n - 1)) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  rw[hn1]
  apply gol

theorem mul_choose_two_pow_from_3_to_4(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n)(hn1 : ∑ l in range n, Nat.choose (n - 1) l = ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l) :
   ∑ l in range n, Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  rw[hn1]
  rw [sum_range_choose]

theorem mul_choose_two_pow_from_4_to_4(n : ℕ)(hn : 0 < n)(n1 : 1 ≤ n)(hn1 : ∑ l in range n, Nat.choose (n - 1) l = ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l) :
   ∑ l in range (n - 1 + 1), Nat.choose (n - 1) l = 2 ^ (n - 1) := by
  rw [sum_range_choose]

