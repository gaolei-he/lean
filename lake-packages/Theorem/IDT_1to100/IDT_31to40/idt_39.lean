import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Parity
#align_import data.nat.choose.sum from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

open Nat

open Finset

open BigOperators

variable {R : Type*}


theorem idt39(n : ℕ)(k : ℕ) : ∑ k in range (n + 1), ((choose n k) * ((1 / (((k + 1):ℝ) * ((k + 2):ℝ))):ℝ)) = (2 ^ (n + 2) - 1) / ((n + 1) * (n + 2)) - 1 / (n + 1):= by
  have hn_neg_zero_1: ((n + 1):ℝ) ≠ 0 := by linarith
  have hn_neg_zero_2: ((n + 2):ℝ) ≠ 0 := by linarith

  have h_choose_nk(k : ℕ): (choose n k) = ((choose (n + 1) (k + 1) * (k + 1))) / (n + 1)  := by
    rw[← succ_mul_choose_eq]
    simp
  have h_choose_nk'(k : ℕ): (choose n k) = choose (n + 1) (k + 1) * (((k + 1)) / (n + 1) :ℝ )  := by
    rw[h_choose_nk k]
    rw[← mul_div_assoc]
    rw[cast_div, cast_mul]
    simp
    have h_mod:  n + 1 ∣ Nat.choose (n + 1) (k + 1) * (k + 1) := by
      rw[← succ_mul_choose_eq]
      simp
    exact h_mod
    rw[cast_add]
    simp
    exact hn_neg_zero_1

  have h_choose1: ∑ k in range (n + 1), ((choose n k) * ((1 / (((k + 1):ℝ) * ((k + 2):ℝ))):ℝ)) = ∑ k in range (n + 1), ((1/(n + 1)) * ((((choose (n + 1) (k + 1))) ) * ((1 / (k + 2)):ℝ))) := by
    refine' sum_congr rfl fun y hy ↦ _
    have hy_neg_zero: (y:ℝ) + 1 ≠ 0 := by linarith
    rw[h_choose_nk' y]
    rw[← mul_assoc]
    rw[mul_comm (1/(n+1): ℝ) (choose (n + 1) (y + 1): ℝ)]
    rw[mul_one_div (choose (n + 1) (y + 1): ℝ) (n+1: ℝ)]
    rw[← mul_div_right_comm]
    rw[←mul_div_assoc]
    rw[mul_one]
    rw[mul_div_assoc,mul_div_assoc]
    congr 1
    rw[div_right_comm]
    rw[← div_div]
    rw[div_self]
    exact hy_neg_zero
  rw[h_choose1]
  rw[← mul_sum]

  have h_choose_succ_succ(k : ℕ): (choose (n+1) (k+1)) = ((choose (n + 2) (k + 2) * (k + 2))) / (n + 2)  := by
    rw[← succ_mul_choose_eq]
    simp
  have h_choose_succ_succ'(k : ℕ): (choose (n+1) (k+1)) = choose (n + 2) (k + 2) * (((k + 2)) / (n + 2) :ℝ )  := by
    rw[h_choose_succ_succ k]
    rw[← mul_div_assoc]
    rw[cast_div, cast_mul]
    simp
    have h_mod:  n + 2 ∣ Nat.choose (n + 2) (k + 2) * (k + 2) := by
      rw[← succ_mul_choose_eq]
      simp
    exact h_mod
    rw[cast_add]
    simp
    exact hn_neg_zero_2

  have h_choose1: ∑ k in range (n + 1), ((((choose (n + 1) (k + 1))) ) * ((1 / (k + 2)):ℝ)) = ∑ k in range (n + 1), ( ((1 / (n + 2)):ℝ) * (((choose (n + 2) (k + 2))) ) ) := by
    refine' sum_congr rfl fun y hy ↦ _
    rw[mul_comm (1/(n+2): ℝ) (choose (n + 2) (y + 2): ℝ)]
    rw[h_choose_succ_succ' y]
    rw[mul_assoc]
    rw[← mul_div_right_comm]
    rw[mul_one_div_cancel]
    have hy_two_neg_zero: (y:ℝ) + 2 ≠ 0 := by linarith
    exact hy_two_neg_zero
  rw[h_choose1]
  rw[← mul_sum]
  rw[← mul_assoc]

  have h11: (∑ x in range (n + 2 + 1), ((Nat.choose (n + 2) x): ℝ)) - (choose (n + 2) 0) = ∑ x in range (n + 1 + 1), (Nat.choose (n + 2) (x + 1): ℝ) := by
    have zero_lt_succ_succ: 0 < n + 1 + 1 := by linarith
    have zero_lt_two: 0 ≤ n + 2 := by linarith
    rw[range_eq_Ico]
    rw[sum_Ico_succ_top]
    simp
    rw[← one_add_one_eq_two,← add_assoc]
    rw[range_eq_Ico]
    rw[sum_eq_sum_Ico_succ_bot]
    have n_succ: 0 ≤ n + 1:= by linarith
    rw[sum_Ico_succ_top n_succ]
    rw[sum_Ico_eq_sum_range]
    rw[add_comm]
    simp
    refine' sum_congr rfl fun y hy ↦ _
    rw[add_comm 1 y]
    exact zero_lt_succ_succ
    exact zero_lt_two

  have h22: (∑ x in range (n + 1 + 1), (Nat.choose (n + 2) (x + 1): ℝ)) - (choose (n + 2) 1) = ∑ x in range (n + 1), (Nat.choose (n + 2) (x + 2): ℝ) := by
    have zero_lt_succ_succ: 0 < n + 1 + 1 := by linarith
    rw[range_eq_Ico]
    rw[sum_eq_sum_Ico_succ_bot]
    rw[add_assoc,add_comm,add_sub_assoc]
    simp
    rw[one_add_one_eq_two,one_add_one_eq_two]
    rw[range_eq_Ico]
    simp
    rw[sum_Ico_eq_sum_range]
    refine' sum_congr rfl fun y hy ↦ _
    rw[add_comm 1 y]
    exact zero_lt_succ_succ

  have choose_sum: ∑ x in range (n + 1), (Nat.choose (n + 2) (x + 2) : ℝ) = (2^(n+2): ℝ) - ((choose (n + 2) 0): ℝ) - ((choose (n + 2) 1): ℝ) := by
    have h'': ∑ x in range (n + 1), (Nat.choose (n + 2) (x + 2): ℝ) = ∑ x in range (n + 2 + 1), (((Nat.choose (n + 2) (x)): ℝ)) - ((choose (n + 2) 0): ℝ) - (choose (n + 2) 1) := by
      rw[← h22, ← h11]
    rw[h'']
    rw[← cast_sum, sum_range_choose]
    simp
  rw[choose_sum]
  rw[one_div_mul_one_div]
  rw[← mul_one_div ((2 ^ (n + 2) - 1):ℝ)  ((n + 1) * (n + 2) : ℝ )]
  rw[choose_zero_right,choose_one_right]
  rw[mul_sub]
  rw[← one_div_mul_one_div]
  rw[cast_add n 2]
  rw[cast_two]
  rw[mul_assoc ((1/(n + 1)):ℝ) ((1/(n + 2)):ℝ) ((n + 2):ℝ)]
  rw[one_div_mul_cancel, mul_one]
  congr 1
  rw[mul_comm]
  simp
  exact hn_neg_zero_2
