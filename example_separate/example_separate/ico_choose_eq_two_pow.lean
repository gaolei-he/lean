import AdaLean.range_choose_eq_ico_choose

open Nat

open Finset

open BigOperators


theorem ico_choose_eq_two_pow(h : 2 ≤ n ) : ∑ s in Ico 0 (n-1), choose (n-2) s = 2 ^ ( n - 2 ) := by
    rw[← range_eq_Ico]
    rw[range_choose_eq_ico_choose h]
    rw[range_eq_Ico]
