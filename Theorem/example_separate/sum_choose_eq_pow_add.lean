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
    have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]  -- an - choose (2 * n) n + an + choose (2 * n) n = 2 ^ ( 2 * n ) + choose (2 * n) n
    have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by -- an - choose (2 * n) n + an + choose (2 * n) n = an + an
      rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
      simp
      rw [Nat.sub_add_cancel choose_le_sum]
    have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   -- an + an = 2 ^ ( 2 * n ) + choose (2 * n) n
      rw[←sum_sub_sum_add,sum_add_eq_add]
    have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  -- 2 * an = 2 ^ ( 2 * n ) + choose (2 * n) n
      rw[← sum_add_eq_two_pow, two_mul]
    have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]  -- an = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2
    have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
    rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]


theorem sum_choose_eq_pow_add_from_0_to_0(n : ℕ)(hn : n ≠ 0)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]
  apply gol

theorem sum_choose_eq_pow_add_from_0_to_1(n : ℕ)(hn : n ≠ 0)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  apply gol

theorem sum_choose_eq_pow_add_from_0_to_2(n : ℕ)(hn : n ≠ 0)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  apply gol

theorem sum_choose_eq_pow_add_from_0_to_3(n : ℕ)(hn : n ≠ 0)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  apply gol

theorem sum_choose_eq_pow_add_from_0_to_4(n : ℕ)(hn : n ≠ 0)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_0_to_5(n : ℕ)(hn : n ≠ 0)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_0_to_6(n : ℕ)(hn : n ≠ 0)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  apply gol

theorem sum_choose_eq_pow_add_from_0_to_7(n : ℕ)(hn : n ≠ 0)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  apply gol

theorem sum_choose_eq_pow_add_from_0_to_8(n : ℕ)(hn : n ≠ 0)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_0_to_9(n : ℕ)(hn : n ≠ 0)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  apply gol

theorem sum_choose_eq_pow_add_from_0_to_10(n : ℕ)(hn : n ≠ 0) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_pow_eq_range_add_ico : 2 ^ ( 2 * n )  = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by rw[ ← sum_eq_two ]
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

theorem sum_choose_eq_pow_add_from_1_to_1(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  apply gol

theorem sum_choose_eq_pow_add_from_1_to_2(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  apply gol

theorem sum_choose_eq_pow_add_from_1_to_3(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  apply gol

theorem sum_choose_eq_pow_add_from_1_to_4(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_1_to_5(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_1_to_6(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  apply gol

theorem sum_choose_eq_pow_add_from_1_to_7(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  apply gol

theorem sum_choose_eq_pow_add_from_1_to_8(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_1_to_9(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  apply gol

theorem sum_choose_eq_pow_add_from_1_to_10(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose : ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) = ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n := by rw[Ico_choose_range_choose]
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

theorem sum_choose_eq_pow_add_from_2_to_2(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  apply gol

theorem sum_choose_eq_pow_add_from_2_to_3(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  apply gol

theorem sum_choose_eq_pow_add_from_2_to_4(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_2_to_5(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_2_to_6(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  apply gol

theorem sum_choose_eq_pow_add_from_2_to_7(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  apply gol

theorem sum_choose_eq_pow_add_from_2_to_8(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_2_to_9(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  apply gol

theorem sum_choose_eq_pow_add_from_2_to_10(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have range_sub_choose_add_sum : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k  = 2 ^ ( 2 * n ) := by       rw[← range_sub_choose, Nat.add_comm]
    rw[← two_pow_eq_range_add_ico]
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

theorem sum_choose_eq_pow_add_from_3_to_3(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  apply gol

theorem sum_choose_eq_pow_add_from_3_to_4(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_3_to_5(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_3_to_6(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  apply gol

theorem sum_choose_eq_pow_add_from_3_to_7(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  apply gol

theorem sum_choose_eq_pow_add_from_3_to_8(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_3_to_9(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  apply gol

theorem sum_choose_eq_pow_add_from_3_to_10(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n)) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have choose_le_sum :choose (2 * n) n ≤ ∑ k in range (n + 1), choose (2 * n) k := by
    rw[sum_range_succ]
    simp
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

theorem sum_choose_eq_pow_add_from_4_to_4(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_4_to_5(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_4_to_6(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  apply gol

theorem sum_choose_eq_pow_add_from_4_to_7(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  apply gol

theorem sum_choose_eq_pow_add_from_4_to_8(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_4_to_9(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  apply gol

theorem sum_choose_eq_pow_add_from_4_to_10(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n =  2 ^ ( 2 * n ) + choose (2 * n) n := by rw[range_sub_choose_add_sum]
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

theorem sum_choose_eq_pow_add_from_5_to_5(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_5_to_6(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  apply gol

theorem sum_choose_eq_pow_add_from_5_to_7(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  apply gol

theorem sum_choose_eq_pow_add_from_5_to_8(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_5_to_9(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  apply gol

theorem sum_choose_eq_pow_add_from_5_to_10(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_sub_sum_add : ∑ k in range (n + 1), choose (2 * n) k - choose (2 * n) n + ∑ k in range (n + 1), choose (2 * n) k + choose (2 * n) n = ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k := by rw [add_assoc,← add_comm (choose (2 * n) n) (∑ k in range (n + 1), choose (2 * n) k), ← add_assoc]
    simp
    rw [Nat.sub_add_cancel choose_le_sum]
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

theorem sum_choose_eq_pow_add_from_6_to_6(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  apply gol

theorem sum_choose_eq_pow_add_from_6_to_7(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  apply gol

theorem sum_choose_eq_pow_add_from_6_to_8(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_6_to_9(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  apply gol

theorem sum_choose_eq_pow_add_from_6_to_10(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_eq_two_pow : ∑ k in range (n + 1), choose (2 * n) k + ∑ k in range (n + 1), choose (2 * n) k =  2 ^ ( 2 * n ) + choose (2 * n) n  := by   rw[←sum_sub_sum_add,sum_add_eq_add]
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

theorem sum_choose_eq_pow_add_from_7_to_7(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_two_pow :  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n) + Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  apply gol

theorem sum_choose_eq_pow_add_from_7_to_8(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_two_pow :  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n) + Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_7_to_9(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_two_pow :  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n) + Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  apply gol

theorem sum_choose_eq_pow_add_from_7_to_10(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_two_pow :  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n) + Nat.choose (2 * n) n) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have two_mul_sum : 2 * ∑ k in range (n + 1), choose (2 * n) k = 2 ^ ( 2 * n ) + choose (2 * n) n := by  rw[← sum_add_eq_two_pow, two_mul]
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

theorem sum_choose_eq_pow_add_from_8_to_8(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_two_pow :  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n) + Nat.choose (2 * n) n)(two_mul_sum : 2 * ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n) + Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  apply gol

theorem sum_choose_eq_pow_add_from_8_to_9(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_two_pow :  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n) + Nat.choose (2 * n) n)(two_mul_sum : 2 * ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n) + Nat.choose (2 * n) n)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  apply gol

theorem sum_choose_eq_pow_add_from_8_to_10(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_two_pow :  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n) + Nat.choose (2 * n) n)(two_mul_sum : 2 * ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n) + Nat.choose (2 * n) n) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have sum_add_div_two : ∑ k in range (n + 1), choose (2 * n) k = (2 ^ ( 2 * n ) + choose (2 * n) n) / 2 := by simp [← two_mul_sum]
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

theorem sum_choose_eq_pow_add_from_9_to_9(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_two_pow :  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n) + Nat.choose (2 * n) n)(two_mul_sum : 2 * ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_add_div_two : ∑ k in range (n + 1), Nat.choose (2 * n) k = (2 ^ (2 * n) + Nat.choose (2 * n) n) / 2)(gol:  ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  apply gol

theorem sum_choose_eq_pow_add_from_9_to_10(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_two_pow :  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n) + Nat.choose (2 * n) n)(two_mul_sum : 2 * ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_add_div_two : ∑ k in range (n + 1), Nat.choose (2 * n) k = (2 ^ (2 * n) + Nat.choose (2 * n) n) / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  have add_div_two_eq_distrib : (choose (2 * n) n + 2 ^ ( 2 * n )) / 2 = 2 ^ ( 2 * n - 1 ) + choose ( 2 * n ) n / 2 := by rw[add_div_two hn]
  rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

theorem sum_choose_eq_pow_add_from_10_to_10(n : ℕ)(hn : n ≠ 0)(two_pow_eq_range_add_ico :  2 ^ (2 * n) = ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k)(range_sub_choose :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(range_sub_choose_add_sum :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n))(choose_le_sum : Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_sub_sum_add :  ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n + ∑ k in range (n + 1), Nat.choose (2 * n) k +      Nat.choose (2 * n) n =    ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k)(sum_add_eq_two_pow :  ∑ k in range (n + 1), Nat.choose (2 * n) k + ∑ k in range (n + 1), Nat.choose (2 * n) k =    2 ^ (2 * n) + Nat.choose (2 * n) n)(two_mul_sum : 2 * ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n) + Nat.choose (2 * n) n)(sum_add_div_two : ∑ k in range (n + 1), Nat.choose (2 * n) k = (2 ^ (2 * n) + Nat.choose (2 * n) n) / 2)(add_div_two_eq_distrib : (Nat.choose (2 * n) n + 2 ^ (2 * n)) / 2 = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2) :
   ∑ k in range (n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n - 1) + Nat.choose (2 * n) n / 2 := by
  rw[ sum_add_div_two, ← add_div_two_eq_distrib, add_comm]

