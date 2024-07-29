import Theorem.example_separate.sum_eq_two
import Theorem.example_separate.Ico_choose_range_choose
import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem sum_choose_eq_pow_add (n : ℕ)(hn : n ≠ 0) :
  ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by
    have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]  -- 2 ^ ( 2 * n ) = an + bn
    have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]   -- bn = an - choose (2 * n) n
    have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       --  2 ^ ( 2 * n ) = bn + an =  an - choose (2 * n) n + an
      rw[← range_sub_choose, Nat.add_comm]
      rw[← two_pow_eq_range_add_ico]
    have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
      rw[sum_range_succ]
      simp
    have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   -- an + an = 2 ^ ( 2 * n ) + choose (2 * n) n
      have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]  -- an - choose (2 * n) n + an + choose (2 * n) n = 2 ^ ( 2 * n ) + choose (2 * n) n
      have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by -- an - choose (2 * n) n + an + choose (2 * n) n = an + an
          rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
          simp
          rw [Nat.sub_add_cancel choose_le_sum]
      rw[←sum_sub_sum_add,sum_add_eq_add]
    have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  -- 2 * an = 2 ^ ( 2 * n ) + choose (2 * n) n
      rw[← sum_add_eq_two_pow, two_mul]
    have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]  -- an = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2
    have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
    rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]
