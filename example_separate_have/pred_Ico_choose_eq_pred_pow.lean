import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators


theorem pred_Ico_choose_eq_pred_pow(h : 2 ≤ n ) :  (n - 1) * ∑ s in Ico 0 (n-1), choose (n-2) s + 2 ^ ( n - 1 ) = (n - 1) * 2 ^ (n-2)  + 2 ^ ( n - 1 ) := by  --sum45
  have ico_choose_eq_two_pow: ∑ s in Ico 0 (n-1), choose (n-2) s = 2 ^ ( n - 2 ) := by
    rw[← range_eq_Ico]
    have range_choose_eq_ico_choose :  ∑ l in range (n-2+1), Nat.choose (n - 2) l = ∑ s in Ico 0 (n-1), choose (n-2) s:= by
      refine' sum_congr _ fun y _ => rfl
      have nn: n - 2 + 1 = n - 1 := by
        exact tsub_add_eq_add_tsub h
      rw[nn,range_eq_Ico]
    rw[sum_range_choose] at range_choose_eq_ico_choose
    rw[range_choose_eq_ico_choose,range_eq_Ico]
  rw[ico_choose_eq_two_pow]
