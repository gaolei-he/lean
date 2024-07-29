import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

theorem sum_choose_eq_pow_add' (n : ℕ)(h : 1 ≤ n) : ∑ k in range (n+1), choose (2*n) k = 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n := by
  have h1 : ∑ k in range (n+1), choose (2*n) k + ∑ k in Ico (n+1) (2*n+1), choose (2*n) k = ((2^(2*n)) : ℝ) := by
    rw [←cast_add]
    rw [sum_range_add_sum_Ico, sum_range_choose (2*n), cast_pow]
    congr 1
    linarith
  have : 0 ≤ n := by exact Nat.zero_le n
  have h3 : ∑ x in range n, Nat.choose (2 * n) (n + 1 + x)
            = ∑ x in range n, Nat.choose (2 * n) (n - 1 - x) := by
      refine' sum_congr rfl fun k hk => _
      rw [←choose_symm, add_assoc, ←Nat.sub_sub, two_mul]
      simp
      rw [Nat.sub_sub]
      rw [mem_range] at hk
      linarith
  have h2 : ∑ k in Ico (n+1) (2*n+1), choose (2*n) k = ∑ k in range (n+1), choose (2*n) k - choose (2*n) n := by
    rw [range_eq_Ico, sum_Ico_succ_top this]
    simp
    rw [sum_Ico_eq_sum_range, two_mul]
    simp
    rw [←two_mul]
    rw [h3, sum_range_reflect (fun x => choose (2*n) x) (n)]
  rw [h2, cast_sub, add_sub, ←two_mul] at h1
  have h3 : 2 * ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) = ((2 ^ (2 * n)) : ℝ) + ↑(Nat.choose (2 * n) n):= by
    rw [←h1, sub_add, sub_self, sub_zero]
  have h4 : ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) = ((1/2):ℝ) * (((2 ^ (2 * n)) : ℝ) + ↑(Nat.choose (2 * n) n)) := by
    rw [←h3,one_div,←mul_assoc]
    simp
  rw [h4, one_div, mul_add]
  congr 1
  have : 2 * n - 1 + 1 = 2*n := by
    rw [Nat.sub_add_cancel]
    linarith
  rw [←this, pow_add, pow_one, mul_comm]
  simp
  rw [sum_range_succ]
  have h6 : 0 ≤ ∑ x in range n, Nat.choose (2 * n) x := by
    exact Nat.zero_le (∑ x in range n, Nat.choose (2 * n) x)
  linarith


theorem sum_choose_eq_pow_add'_from_1_to_1(n : ℕ)(h : 1 ≤ n)(h1 :  ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) + ↑(∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k) = 2 ^ (2 * n))(gol:  ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) = 2 ^ (2 * n - 1) + 1 / 2 * ↑(Nat.choose (2 * n) n)) :
   ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) = 2 ^ (2 * n - 1) + 1 / 2 * ↑(Nat.choose (2 * n) n) := by
  have : 0 ≤ n := by exact Nat.zero_le n
  apply gol

theorem sum_choose_eq_pow_add'_from_3_to_3(n : ℕ)(h : 1 ≤ n)(h1 :  ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) + ↑(∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k) = 2 ^ (2 * n))(this : 0 ≤ n)(h3 : ∑ x in range n, Nat.choose (2 * n) (n + 1 + x) = ∑ x in range n, Nat.choose (2 * n) (n - 1 - x))(gol:  ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) = 2 ^ (2 * n - 1) + 1 / 2 * ↑(Nat.choose (2 * n) n)) :
   ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) = 2 ^ (2 * n - 1) + 1 / 2 * ↑(Nat.choose (2 * n) n) := by
  have h2 : ∑ k in Ico (n+1) (2*n+1), choose (2*n) k = ∑ k in range (n+1), choose (2*n) k - choose (2*n) n := by
    rw [range_eq_Ico, sum_Ico_succ_top this]
    simp
    rw [sum_Ico_eq_sum_range, two_mul]
    simp
    rw [←two_mul]
    rw [h3, sum_range_reflect (fun x => choose (2*n) x) (n)]
  apply gol

theorem sum_choose_eq_pow_add'_from_12_to_12(n : ℕ)(h : 1 ≤ n)(h1 :  ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) + ↑(∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n) =    2 ^ (2 * n))(this : 0 ≤ n)(h3 : ∑ x in range n, Nat.choose (2 * n) (n + 1 + x) = ∑ x in range n, Nat.choose (2 * n) (n - 1 - x))(h2 :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(gol:  Nat.choose (2 * n) n ≤ ∑ x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n) :
   Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k := by
  rw [sum_range_succ]
  apply gol

theorem sum_choose_eq_pow_add'_from_12_to_13(n : ℕ)(h : 1 ≤ n)(h1 :  ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) + ↑(∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n) =    2 ^ (2 * n))(this : 0 ≤ n)(h3 : ∑ x in range n, Nat.choose (2 * n) (n + 1 + x) = ∑ x in range n, Nat.choose (2 * n) (n - 1 - x))(h2 :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(gol:  Nat.choose (2 * n) n ≤ ∑ x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n) :
   Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k := by
  rw [sum_range_succ]
  have h6 : 0 ≤ ∑ x in range n, Nat.choose (2 * n) x := by
    exact Nat.zero_le (∑ x in range n, Nat.choose (2 * n) x)
  apply gol

theorem sum_choose_eq_pow_add'_from_12_to_14(n : ℕ)(h : 1 ≤ n)(h1 :  ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) + ↑(∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n) =    2 ^ (2 * n))(this : 0 ≤ n)(h3 : ∑ x in range n, Nat.choose (2 * n) (n + 1 + x) = ∑ x in range n, Nat.choose (2 * n) (n - 1 - x))(h2 :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n) :
   Nat.choose (2 * n) n ≤ ∑ k in range (n + 1), Nat.choose (2 * n) k := by
  rw [sum_range_succ]
  have h6 : 0 ≤ ∑ x in range n, Nat.choose (2 * n) x := by
    exact Nat.zero_le (∑ x in range n, Nat.choose (2 * n) x)
  linarith

theorem sum_choose_eq_pow_add'_from_13_to_13(n : ℕ)(h : 1 ≤ n)(h1 :  ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) + ↑(∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n) =    2 ^ (2 * n))(this : 0 ≤ n)(h3 : ∑ x in range n, Nat.choose (2 * n) (n + 1 + x) = ∑ x in range n, Nat.choose (2 * n) (n - 1 - x))(h2 :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(gol:  Nat.choose (2 * n) n ≤ ∑ x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n) :
   Nat.choose (2 * n) n ≤ ∑ x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n := by
  have h6 : 0 ≤ ∑ x in range n, Nat.choose (2 * n) x := by
    exact Nat.zero_le (∑ x in range n, Nat.choose (2 * n) x)
  apply gol

theorem sum_choose_eq_pow_add'_from_13_to_14(n : ℕ)(h : 1 ≤ n)(h1 :  ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) + ↑(∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n) =    2 ^ (2 * n))(this : 0 ≤ n)(h3 : ∑ x in range n, Nat.choose (2 * n) (n + 1 + x) = ∑ x in range n, Nat.choose (2 * n) (n - 1 - x))(h2 :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n) :
   Nat.choose (2 * n) n ≤ ∑ x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n := by
  have h6 : 0 ≤ ∑ x in range n, Nat.choose (2 * n) x := by
    exact Nat.zero_le (∑ x in range n, Nat.choose (2 * n) x)
  linarith

theorem sum_choose_eq_pow_add'_from_14_to_14(n : ℕ)(h : 1 ≤ n)(h1 :  ↑(∑ k in range (n + 1), Nat.choose (2 * n) k) + ↑(∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n) =    2 ^ (2 * n))(this : 0 ≤ n)(h3 : ∑ x in range n, Nat.choose (2 * n) (n + 1 + x) = ∑ x in range n, Nat.choose (2 * n) (n - 1 - x))(h2 :  ∑ k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k =    ∑ k in range (n + 1), Nat.choose (2 * n) k - Nat.choose (2 * n) n)(h6 : 0 ≤ ∑ x in range n, Nat.choose (2 * n) x) :
   Nat.choose (2 * n) n ≤ ∑ x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n := by
  linarith

