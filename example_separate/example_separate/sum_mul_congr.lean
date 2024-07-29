import AdaLean.add_div_two

open Nat

open Finset

open BigOperators

theorem sum_mul_congr : ∑ k in Ico 1 (n + 1), n * choose (n-1) (k-1) = n * ∑ l in range n, choose (n-1) l := by
  rw[mul_sum]
  rw[sum_Ico_eq_sum_range]
  simp
