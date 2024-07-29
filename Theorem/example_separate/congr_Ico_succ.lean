import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem congr_Ico_succ:
  ∑ k in Ico 1 (n + 1), k * choose (n-1) (k-1) = ∑ l in Ico 0 n, (l + 1) * choose (n-1) l:= by
  rw[sum_Ico_eq_sum_range]
  simp
  refine' sum_congr rfl fun y _ => _
  rw[add_comm]


theorem congr_Ico_succ_from_0_to_0(n : ℕ)(gol:  ∑ k in range (n + 1 - 1), (1 + k) * Nat.choose (n - 1) (1 + k - 1) = ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l) :
   ∑ k in Ico 1 (n + 1), k * Nat.choose (n - 1) (k - 1) = ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l := by
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem congr_Ico_succ_from_0_to_1(n : ℕ)(gol:  ∑ x in range n, (1 + x) * Nat.choose (n - 1) x = ∑ x in range n, (x + 1) * Nat.choose (n - 1) x) :
   ∑ k in Ico 1 (n + 1), k * Nat.choose (n - 1) (k - 1) = ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l := by
  rw[sum_Ico_eq_sum_range]
  simp
  apply gol

theorem congr_Ico_succ_from_1_to_1(n : ℕ)(gol:  ∑ x in range n, (1 + x) * Nat.choose (n - 1) x = ∑ x in range n, (x + 1) * Nat.choose (n - 1) x) :
   ∑ k in range (n + 1 - 1), (1 + k) * Nat.choose (n - 1) (1 + k - 1) = ∑ l in Ico 0 n, (l + 1) * Nat.choose (n - 1) l := by
  simp
  apply gol

theorem congr_Ico_succ_from_3_to_3(n y : ℕ)(x : y ∈ range n) :
   (1 + y) * Nat.choose (n - 1) y = (y + 1) * Nat.choose (n - 1) y := by
  rw[add_comm]
