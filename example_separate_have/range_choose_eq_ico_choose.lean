import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators


theorem range_choose_eq_ico_choose(h : 2 ≤ n )  :  ∑ l in range (n-2+1), Nat.choose (n - 2) l = ∑ s in Ico 0 (n-1), choose (n-2) s:= by
      refine' sum_congr _ fun y _ => rfl
      have sub_two_add_one: n - 2 + 1 = n - 1 := by
        exact tsub_add_eq_add_tsub h
      rw[sub_two_add_one,range_eq_Ico]
