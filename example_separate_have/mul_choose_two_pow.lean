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
