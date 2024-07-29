import AdaLean.add_div_two

open Nat

open Finset

open BigOperators

theorem mul_choose_two_pow(hn : 0 < n) : n * ∑ l in range n, choose (n-1) l = n * 2 ^ (n-1) := by
  congr 1
  have n1 : 1 ≤ n := by linarith
  rw[← Nat.sub_add_cancel n1]
  simp
  rw [sum_range_choose]
