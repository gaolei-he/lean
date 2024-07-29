import Theorem.example_separate.sum_mul_choose_eq_mul_two_pow
import Theorem.example_separate.sum_choose_eq_pow_add'
import Theorem.mini_separate.one_div_two_mul_choose_sub_succ_mul_choose
open Nat

open Finset

open BigOperators



theorem sum_mul_choose_eq_two_pow' (n : ℕ) (h : 1 ≤ n) :((∑ k in range (n+1), k * choose (2*n+1) k):ℝ)
                        = ((n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n) : ℝ) :=
  have h_gt_zero : 0 < n + 1 := by linarith
  have h1 : ∑ k in Ico 1 (n + 1), k * choose (2*n) k = ∑ k in range (n+1), k * choose (2*n) k := by
    rw [range_eq_Ico]
    rw [sum_eq_sum_Ico_succ_bot h_gt_zero]
    simp
  have h2 : ∑ k in Ico 1 (n + 1), k * choose (2*n) (k-1)
          = ∑ k in range (n+1), (k+1) * choose (2*n) k - (n+1) * choose (2*n) n := by
    rw [sum_Ico_eq_sum_range, sum_range_succ]
    simp [add_comm]
  have h3 : ∑ k in range (n+1), (k+1) * choose (2*n) k
          = ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k := by
    rw [←sum_add_distrib]
    refine' sum_congr rfl fun k hk => _
    rw [add_mul]
    simp
  calc
    ((∑ k in range (n+1), k * choose (2*n+1) k) : ℝ) = ∑ k in Ico 1 (n + 1), k * choose (2*n+1) k := by
      {
        rw [range_eq_Ico]
        rw [sum_eq_sum_Ico_succ_bot h_gt_zero]
        simp
      }
    _ = ∑ k in Ico 1 (n + 1), k * (choose (2*n) k + choose (2*n) (k-1)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        congr 1
        have : k = k-1+1 := by
          rw [Nat.sub_add_cancel]
          rw [mem_Ico] at hk
          exact hk.left
        rw [this, choose_succ_succ' (2*n) (k-1), ←this, add_comm]
      }
    _ = ∑ k in Ico 1 (n + 1), (k * choose (2*n) k + k * choose (2*n) (k-1)) := by
      {
        congr 1
        refine' sum_congr rfl fun k hk => _
        rw [mul_add]
      }
    _ = ∑ k in Ico 1 (n + 1), k * choose (2*n) k + ∑ k in Ico 1 (n + 1), k * choose (2*n) (k-1) := by
      {
        rw [←cast_add]
        congr 1
        rw [sum_add_distrib]
      }
    _ = ∑ k in range (n+1), k * choose (2*n) k
      + ∑ k in range (n+1), k * choose (2*n) k + ∑ k in range (n+1), choose (2*n) k - (n+(1:ℕ)) * choose (2*n) n := by
      {
        rw [h1, h2]
        rw [cast_sub, ←add_sub_assoc]
        congr 1
        rw [add_assoc]
        congr 1
        rw [h3, cast_add]
        rw [←cast_add, ←cast_mul]
        rw [sum_range_succ]
        have : 0 ≤ ∑ k in range n, (k + 1) * Nat.choose (2 * n) k := by
          exact Nat.zero_le (∑ k in range n, (k + 1) * Nat.choose (2 * n) k)
        linarith
      }
    _ = 2*(n:ℝ)*2^(2*n-1) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n := by
      {
        have : 0 < n := by linarith
        have h1 : n ≠ 0 := by linarith
        rw [←two_mul, sum_mul_choose_eq_mul_two_pow this, sum_choose_eq_pow_add' n h]
        congr 1
        rw [cast_mul, ←mul_assoc, ←add_assoc]
        congr 3
        rw [cast_pow]
        congr 1
        congr 2
        rw [cast_one]
      }
    _ = n*2^(2*n) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n := by
      {
        congr 3
        rw [←cast_comm, mul_assoc]
        congr 1
        have : 2*n = 2*n-1+1 := by
          have : 1 ≤ 2*n := by rw [two_mul]; linarith
          rw [Nat.sub_add_cancel this]
        rw [this, pow_add, ←this, pow_one, mul_comm]
      }
    _ = n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n := by
      {
        rw [add_sub_assoc]
        rw [one_div_two_mul_choose_sub_succ_mul_choose n h]
        congr 1
        rw [←neg_one_mul ((2 * n + 1) * (Nat.choose (2 * n - 1) n) : ℝ)]
        rw [←mul_assoc, neg_one_mul]
      }


theorem sum_mul_choose_eq_two_pow'_from_0_to_0(n : ℕ)(h : 1 ≤ n) :
   0 < n + 1 := by
  linarith

