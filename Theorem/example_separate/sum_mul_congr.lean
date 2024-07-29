import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem sum_mul_congr : ∑ k in Ico 1 (n + 1), n * choose (n-1) (k-1) = n * ∑ l in range n, choose (n-1) l := by
  rw[mul_sum]   --先把 n 提出来
  rw[sum_Ico_eq_sum_range]  -- 代换 l = k - 1
  simp


theorem sum_mul_congr_from_0_to_0(n : ℕ)(gol:  ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) = ∑ x in range n, n * Nat.choose (n - 1) x) :
   ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) = n * ∑ l in range n, Nat.choose (n - 1) l := by
  rw[mul_sum]
  apply gol

theorem sum_mul_congr_from_0_to_1(n : ℕ)(gol:  ∑ k in range (n + 1 - 1), n * Nat.choose (n - 1) (1 + k - 1) = ∑ x in range n, n * Nat.choose (n - 1) x) :
   ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) = n * ∑ l in range n, Nat.choose (n - 1) l := by
  rw[mul_sum]
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem sum_mul_congr_from_0_to_2(n : ℕ) :
   ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) = n * ∑ l in range n, Nat.choose (n - 1) l := by
  rw[mul_sum]
  rw[sum_Ico_eq_sum_range]
  simp

theorem sum_mul_congr_from_1_to_1(n : ℕ)(gol:  ∑ k in range (n + 1 - 1), n * Nat.choose (n - 1) (1 + k - 1) = ∑ x in range n, n * Nat.choose (n - 1) x) :
   ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) = ∑ x in range n, n * Nat.choose (n - 1) x := by
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem sum_mul_congr_from_1_to_2(n : ℕ) :
   ∑ k in Ico 1 (n + 1), n * Nat.choose (n - 1) (k - 1) = ∑ x in range n, n * Nat.choose (n - 1) x := by
  rw[sum_Ico_eq_sum_range]
  simp

theorem sum_mul_congr_from_2_to_2(n : ℕ) :
   ∑ k in range (n + 1 - 1), n * Nat.choose (n - 1) (1 + k - 1) = ∑ x in range n, n * Nat.choose (n - 1) x := by
  simp

