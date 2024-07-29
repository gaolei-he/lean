import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators


theorem sum_range_choose_halfway_of_lt (n : ℕ) (h0 : 0 < n): ∑ k in range n, choose (2 * n - 1) k = 2^(2 * n - 2) :=
  have : ∑ k in range n, choose (2 * n - 1) k = ∑ k in Ico n (2 * n), choose (2 * n - 1) k := by
    have h1 : ∑ k in range n, choose (2 * n - 1) k
            = ∑ k in range n, choose (2 * n - 1) (2 * n - 1 - k) := by
      refine' sum_congr rfl fun y hy => _
      have : y ≤ 2 * n - 1 := by
        have h1 : y < n := mem_range.1 hy
        refine le_pred_of_lt ?h
        have h2 : n < 2 * n := by exact lt_two_mul_self h0
        exact Nat.lt_trans h1 h2
      rw [choose_symm this]
    rw [h1, range_eq_Ico]
    have : n ≤ 2 * n - 1 + 1 := by
      have : 1 ≤ 2 * n := by linarith
      rw [Nat.sub_add_cancel this]
      linarith
    rw [sum_Ico_reflect _ _ this]
    have h2 : 2 * n - 1 + 1 - n = n := by
      have : 1 ≤ 2 * n := by linarith
      rw [Nat.sub_add_cancel this]
      rw [two_mul]
      simp
    have h3 : 2 * n - 1 + 1 - 0 = 2 * n := by
      simp
      have : 1 ≤ 2 * n := by linarith
      rw [Nat.sub_add_cancel this]
    rw [h2, h3]
  mul_right_injective₀ two_ne_zero <|
    calc
      2 * (∑ k in range n, choose (2 * n - 1) k)
        = ∑ k in range n, choose (2 * n - 1) k + ∑ k in Ico n (2 * n), choose (2 * n - 1) k := by rw [two_mul, this]
      _ =  ∑ k in range (2 * n), choose (2 * n - 1) k := sum_range_add_sum_Ico _ (by linarith)
      _ = ∑ k in range (2 * n - 1 + 1), choose (2 * n - 1) k := by
          {
            have : 1 ≤ 2 * n := by linarith
            rw [Nat.sub_add_cancel this]
          }
      _ = 2^(2 * n - 1) := sum_range_choose (2 * n - 1)
      _ = 2^(2 * n - 2 + 1)  := by
          {
            congr 1
            rw [←tsub_tsub_assoc]
            linarith
            linarith
          }
      _ = 2 * 2^(2 * n - 2)  := by rw [Nat.pow_succ, mul_comm]
