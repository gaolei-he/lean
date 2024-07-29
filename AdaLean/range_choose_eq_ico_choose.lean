import AdaLean.add_div_two

open Nat

open Finset

open BigOperators


theorem range_choose_eq_ico_choose (h : 2 ≤ n ):  2 ^ (n - 2)  = ∑ s in Ico 0 (n-1), choose (n-2) s:= by
  rw[← sum_range_choose]
  refine' sum_congr _ fun y _ => rfl
  rw[range_eq_Ico]
  congr 1
  exact tsub_add_eq_add_tsub h
