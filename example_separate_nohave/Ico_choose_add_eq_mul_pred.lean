import Theorem.example_separate.add_div_two
import Theorem.example_separate.choose_mul_eq_mul_sub

open Nat

open Finset

open BigOperators

theorem Ico_choose_add_eq_mul_pred(hn0 : 0 < n) : ∑ l in Ico 1 n, l * choose (n-1) l + 2 ^ ( n - 1 ) = (n - 1) * ∑ l in Ico 1 (n), choose (n-2) (l-1) + 2 ^ ( n - 1 ):= by --sum43
    have mul_choose_sub {l : ℕ }(hh1: l ≤ n - 1)(hh2: 1 ≤ l) :
    l * choose ( n - 1 ) l = (n - 1) * choose (n-2) (l-1) := by
      rw[mul_comm]
      rw[choose_mul_eq_mul_sub (hh1) (hh2)]
      rw[Nat.sub_sub, Nat.sub_one]
    have ico_mul_choose_sub : ∑ l in Ico 1 n ,l * choose (n-1) l  = ∑ l in Ico 1 n, (n - 1) * choose (n-2) (l-1) := by
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
    rw[ico_mul_choose_sub]
    rw[← mul_sum]
