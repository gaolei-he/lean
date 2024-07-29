import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators


theorem ico_choose_eq_two_pow(h : 2 ≤ n ) : ∑ s in Ico 0 (n-1), choose (n-2) s = 2 ^ ( n - 2 ) := by
    rw[← range_eq_Ico]
    have nn: n - 2 + 1 = n - 1 := by
        exact tsub_add_eq_add_tsub h
    have range_choose_eq_ico_choose :  ∑ l in range (n-2+1), Nat.choose (n - 2) l = ∑ s in Ico 0 (n-1), choose (n-2) s:= by
      refine' sum_congr _ fun y _ => rfl
      rw[nn,range_eq_Ico]
    rw[sum_range_choose] at range_choose_eq_ico_choose
    rw[range_choose_eq_ico_choose,range_eq_Ico]


theorem ico_choose_eq_two_pow_from_0_to_0(n : ℕ)(h : 2 ≤ n)(gol:  ∑ s in range (n - 1), Nat.choose (n - 2) s = 2 ^ (n - 2)) :
   ∑ s in Ico 0 (n - 1), Nat.choose (n - 2) s = 2 ^ (n - 2) := by
  rw[← range_eq_Ico]
  apply gol

theorem ico_choose_eq_two_pow_from_0_to_1(n : ℕ)(h : 2 ≤ n)(gol:  ∑ s in range (n - 1), Nat.choose (n - 2) s = 2 ^ (n - 2)) :
   ∑ s in Ico 0 (n - 1), Nat.choose (n - 2) s = 2 ^ (n - 2) := by
  rw[← range_eq_Ico]
  have nn: n - 2 + 1 = n - 1 := by
      exact tsub_add_eq_add_tsub h
  apply gol

theorem ico_choose_eq_two_pow_from_1_to_1(n : ℕ)(h : 2 ≤ n)(gol:  ∑ s in range (n - 1), Nat.choose (n - 2) s = 2 ^ (n - 2)) :
   ∑ s in range (n - 1), Nat.choose (n - 2) s = 2 ^ (n - 2) := by
  have nn: n - 2 + 1 = n - 1 := by
      exact tsub_add_eq_add_tsub h
  apply gol

theorem ico_choose_eq_two_pow_from_3_to_3(n : ℕ)(h : 2 ≤ n)(nn : n - 2 + 1 = n - 1)(range_choose_eq_ico_choose : ∑ l in range (n - 2 + 1), Nat.choose (n - 2) l = ∑ s in Ico 0 (n - 1), Nat.choose (n - 2) s)(gol:  ∑ s in range (n - 1), Nat.choose (n - 2) s = 2 ^ (n - 2)) :
   ∑ s in range (n - 1), Nat.choose (n - 2) s = 2 ^ (n - 2) := by
  rw[sum_range_choose] at range_choose_eq_ico_choose
  apply gol

theorem ico_choose_eq_two_pow_from_3_to_4(n : ℕ)(h : 2 ≤ n)(nn : n - 2 + 1 = n - 1)(range_choose_eq_ico_choose : ∑ l in range (n - 2 + 1), Nat.choose (n - 2) l = ∑ s in Ico 0 (n - 1), Nat.choose (n - 2) s) :
   ∑ s in range (n - 1), Nat.choose (n - 2) s = 2 ^ (n - 2) := by
  rw[sum_range_choose] at range_choose_eq_ico_choose
  rw[range_choose_eq_ico_choose,range_eq_Ico]

theorem ico_choose_eq_two_pow_from_4_to_4(n : ℕ)(h : 2 ≤ n)(nn : n - 2 + 1 = n - 1)(range_choose_eq_ico_choose : 2 ^ (n - 2) = ∑ s in Ico 0 (n - 1), Nat.choose (n - 2) s) :
   ∑ s in range (n - 1), Nat.choose (n - 2) s = 2 ^ (n - 2) := by
  rw[range_choose_eq_ico_choose,range_eq_Ico]

