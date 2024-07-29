import Theorem.example_separate.mul_choose_sub

open Nat

open Finset

open BigOperators

theorem ico_mul_choose_sub(hn0 : 0 < n) : ∑ l in Ico 1 n ,l * choose (n-1) l  = ∑ l in Ico 1 n, (n - 1) * choose (n-2) (l-1) := by
  refine' sum_congr rfl fun y hy ↦ _
  have hyn : y < n := by exact (mem_Ico.1 hy).2
  have lt_eq_le_sub : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[mul_choose_sub hy_sub_1 hy1]
