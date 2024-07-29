import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem range_eq_ico_mul_choose:  ∑ k in range ( n + 1 ), k * choose n k = ∑ k in Ico 1 (n + 1), k * choose n k := by   -- 更改 k 的范围
  rw[range_eq_Ico]
  have h_succ : 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h_succ]
  simp
