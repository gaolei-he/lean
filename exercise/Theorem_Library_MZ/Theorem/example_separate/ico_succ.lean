import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators


theorem ico_succ: ∑ s in Ico 0 (n-1), choose (n-2) s = ∑ l in Ico 1 n, choose (n-2) (l-1) := by
    rw[sum_Ico_eq_sum_range]
    simp
    rw[sum_Ico_eq_sum_range]
    refine' sum_congr rfl fun y _ => _
    simp


theorem ico_succ_from_0_to_0(n : ℕ)(gol:  ∑ k in range (n - 1 - 0), Nat.choose (n - 2) (0 + k) = ∑ l in Ico 1 n, Nat.choose (n - 2) (l - 1)) :
   ∑ s in Ico 0 (n - 1), Nat.choose (n - 2) s = ∑ l in Ico 1 n, Nat.choose (n - 2) (l - 1) := by
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem ico_succ_from_0_to_1(n : ℕ)(gol:  ∑ x in range (n - 1), Nat.choose (n - 2) x = ∑ l in Ico 1 n, Nat.choose (n - 2) (l - 1)) :
   ∑ s in Ico 0 (n - 1), Nat.choose (n - 2) s = ∑ l in Ico 1 n, Nat.choose (n - 2) (l - 1) := by
  rw[sum_Ico_eq_sum_range]
  simp
  apply gol

theorem ico_succ_from_0_to_2(n : ℕ)(gol:  ∑ x in range (n - 1), Nat.choose (n - 2) x = ∑ k in range (n - 1), Nat.choose (n - 2) (1 + k - 1)) :
   ∑ s in Ico 0 (n - 1), Nat.choose (n - 2) s = ∑ l in Ico 1 n, Nat.choose (n - 2) (l - 1) := by
  rw[sum_Ico_eq_sum_range]
  simp
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem ico_succ_from_1_to_1(n : ℕ)(gol:  ∑ x in range (n - 1), Nat.choose (n - 2) x = ∑ l in Ico 1 n, Nat.choose (n - 2) (l - 1)) :
   ∑ k in range (n - 1 - 0), Nat.choose (n - 2) (0 + k) = ∑ l in Ico 1 n, Nat.choose (n - 2) (l - 1) := by
  simp
  apply gol

theorem ico_succ_from_1_to_2(n : ℕ)(gol:  ∑ x in range (n - 1), Nat.choose (n - 2) x = ∑ k in range (n - 1), Nat.choose (n - 2) (1 + k - 1)) :
   ∑ k in range (n - 1 - 0), Nat.choose (n - 2) (0 + k) = ∑ l in Ico 1 n, Nat.choose (n - 2) (l - 1) := by
  simp
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem ico_succ_from_2_to_2(n : ℕ)(gol:  ∑ x in range (n - 1), Nat.choose (n - 2) x = ∑ k in range (n - 1), Nat.choose (n - 2) (1 + k - 1)) :
   ∑ x in range (n - 1), Nat.choose (n - 2) x = ∑ l in Ico 1 n, Nat.choose (n - 2) (l - 1) := by
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem ico_succ_from_4_to_4(n y : ℕ)(x✝ : y ∈ range (n - 1)) :
   Nat.choose (n - 2) y = Nat.choose (n - 2) (1 + y - 1) := by
  simp

