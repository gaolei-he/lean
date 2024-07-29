import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators


theorem sum_range_succ_eq_sum_range : ∑ k in range (n+1), (k * choose (2 * n) k) = (2 * n) * ∑ k in range n, (choose (2*n - 1) k) := by
  rw[range_eq_Ico]
  have h01: 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h01]
  simp
  have h1: ∑ k in Ico 1 (n+1), k * (choose (2 * n) k) = ∑ k in Ico 1 (n+1), (2 * n) * (choose (2*n - 1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
    have hkn: y ≤ 2 * n := by linarith
    have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[choose_mul_eq_mul_sub' hkn hsk]
  rw[h1]
  rw[mul_sum] -- 提出 2 * n + 1
  rw[sum_Ico_eq_sum_range] -- 代换 l = k - 1
  simp --∑ k in range (n+1), (k * choose (2 * n) k) = (2 * n) * ∑ k in range n, (choose (2*n - 1) k)


theorem sum_range_succ_eq_sum_range_from_0_to_0(n : ℕ)(gol:  ∑ k in Ico 0 (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k) :
   ∑ k in range (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in range n, Nat.choose (2 * n - 1) k := by
  rw[range_eq_Ico]
  apply gol

theorem sum_range_succ_eq_sum_range_from_0_to_1(n : ℕ)(gol:  ∑ k in Ico 0 (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k) :
   ∑ k in range (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in range n, Nat.choose (2 * n - 1) k := by
  rw[range_eq_Ico]
  have h01: 0 < n + 1 := by linarith
  apply gol

theorem sum_range_succ_eq_sum_range_from_0_to_2(n : ℕ)(gol:  0 * Nat.choose (2 * n) 0 + ∑ k in Ico (0 + 1) (n + 1), k * Nat.choose (2 * n) k =
    2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k) :
   ∑ k in range (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in range n, Nat.choose (2 * n - 1) k := by
  rw[range_eq_Ico]
  have h01: 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h01]
  apply gol

theorem sum_range_succ_eq_sum_range_from_0_to_3(n : ℕ)(gol:  ∑ x in Ico 1 (n + 1), x * Nat.choose (2 * n) x = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x) :
   ∑ k in range (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in range n, Nat.choose (2 * n - 1) k := by
  rw[range_eq_Ico]
  have h01: 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h01]
  simp
  apply gol

theorem sum_range_succ_eq_sum_range_from_1_to_1(n : ℕ)(gol:  ∑ k in Ico 0 (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k) :
   ∑ k in Ico 0 (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k := by
  have h01: 0 < n + 1 := by linarith
  apply gol

theorem sum_range_succ_eq_sum_range_from_1_to_2(n : ℕ)(gol:  0 * Nat.choose (2 * n) 0 + ∑ k in Ico (0 + 1) (n + 1), k * Nat.choose (2 * n) k =
    2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k) :
   ∑ k in Ico 0 (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k := by
  have h01: 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h01]
  apply gol

theorem sum_range_succ_eq_sum_range_from_1_to_3(n : ℕ)(gol:  ∑ x in Ico 1 (n + 1), x * Nat.choose (2 * n) x = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x) :
   ∑ k in Ico 0 (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k := by
  have h01: 0 < n + 1 := by linarith
  rw [sum_eq_sum_Ico_succ_bot h01]
  simp
  apply gol

theorem sum_range_succ_eq_sum_range_from_2_to_2(n : ℕ)(h01 : 0 < n + 1)(gol:  0 * Nat.choose (2 * n) 0 + ∑ k in Ico (0 + 1) (n + 1), k * Nat.choose (2 * n) k =
    2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k) :
   ∑ k in Ico 0 (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k := by
  rw [sum_eq_sum_Ico_succ_bot h01]
  apply gol

theorem sum_range_succ_eq_sum_range_from_2_to_3(n : ℕ)(h01 : 0 < n + 1)(gol:  ∑ x in Ico 1 (n + 1), x * Nat.choose (2 * n) x = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x) :
   ∑ k in Ico 0 (n + 1), k * Nat.choose (2 * n) k = 2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k := by
  rw [sum_eq_sum_Ico_succ_bot h01]
  simp
  apply gol

theorem sum_range_succ_eq_sum_range_from_3_to_3(n : ℕ)(h01 : 0 < n + 1)(gol:  ∑ x in Ico 1 (n + 1), x * Nat.choose (2 * n) x = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x) :
   0 * Nat.choose (2 * n) 0 + ∑ k in Ico (0 + 1) (n + 1), k * Nat.choose (2 * n) k =
    2 * n * ∑ k in Ico 0 n, Nat.choose (2 * n - 1) k := by
  simp
  apply gol

theorem sum_range_succ_eq_sum_range_from_5_to_5(n : ℕ)(h01 : 0 < n + 1)(h1 : ∑ k in Ico 1 (n + 1), k * Nat.choose (2 * n) k = ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1))(gol:  ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1) = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x) :
   ∑ x in Ico 1 (n + 1), x * Nat.choose (2 * n) x = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x := by
  rw[h1]
  apply gol

theorem sum_range_succ_eq_sum_range_from_5_to_6(n : ℕ)(h01 : 0 < n + 1)(h1 : ∑ k in Ico 1 (n + 1), k * Nat.choose (2 * n) k = ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1))(gol:  ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1) = ∑ x in range n, 2 * n * Nat.choose (2 * n - 1) x) :
   ∑ x in Ico 1 (n + 1), x * Nat.choose (2 * n) x = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x := by
  rw[h1]
  rw[mul_sum]
  apply gol

theorem sum_range_succ_eq_sum_range_from_5_to_7(n : ℕ)(h01 : 0 < n + 1)(h1 : ∑ k in Ico 1 (n + 1), k * Nat.choose (2 * n) k = ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1))(gol:  ∑ k in range (n + 1 - 1), 2 * n * Nat.choose (2 * n - 1) (1 + k - 1) =
    ∑ x in range n, 2 * n * Nat.choose (2 * n - 1) x) :
   ∑ x in Ico 1 (n + 1), x * Nat.choose (2 * n) x = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x := by
  rw[h1]
  rw[mul_sum]
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem sum_range_succ_eq_sum_range_from_5_to_8(n : ℕ)(h01 : 0 < n + 1)(h1 : ∑ k in Ico 1 (n + 1), k * Nat.choose (2 * n) k = ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1)) :
   ∑ x in Ico 1 (n + 1), x * Nat.choose (2 * n) x = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x := by
  rw[h1]
  rw[mul_sum]
  rw[sum_Ico_eq_sum_range]
  simp

theorem sum_range_succ_eq_sum_range_from_6_to_6(n : ℕ)(h01 : 0 < n + 1)(h1 : ∑ k in Ico 1 (n + 1), k * Nat.choose (2 * n) k = ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1))(gol:  ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1) = ∑ x in range n, 2 * n * Nat.choose (2 * n - 1) x) :
   ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1) = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x := by
  rw[mul_sum]
  apply gol

theorem sum_range_succ_eq_sum_range_from_6_to_7(n : ℕ)(h01 : 0 < n + 1)(h1 : ∑ k in Ico 1 (n + 1), k * Nat.choose (2 * n) k = ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1))(gol:  ∑ k in range (n + 1 - 1), 2 * n * Nat.choose (2 * n - 1) (1 + k - 1) =
    ∑ x in range n, 2 * n * Nat.choose (2 * n - 1) x) :
   ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1) = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x := by
  rw[mul_sum]
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem sum_range_succ_eq_sum_range_from_6_to_8(n : ℕ)(h01 : 0 < n + 1)(h1 : ∑ k in Ico 1 (n + 1), k * Nat.choose (2 * n) k = ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1)) :
   ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1) = 2 * n * ∑ x in range n, Nat.choose (2 * n - 1) x := by
  rw[mul_sum]
  rw[sum_Ico_eq_sum_range]
  simp

theorem sum_range_succ_eq_sum_range_from_7_to_7(n : ℕ)(h01 : 0 < n + 1)(h1 : ∑ k in Ico 1 (n + 1), k * Nat.choose (2 * n) k = ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1))(gol:  ∑ k in range (n + 1 - 1), 2 * n * Nat.choose (2 * n - 1) (1 + k - 1) =
    ∑ x in range n, 2 * n * Nat.choose (2 * n - 1) x) :
   ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1) = ∑ x in range n, 2 * n * Nat.choose (2 * n - 1) x := by
  rw[sum_Ico_eq_sum_range]
  apply gol

theorem sum_range_succ_eq_sum_range_from_7_to_8(n : ℕ)(h01 : 0 < n + 1)(h1 : ∑ k in Ico 1 (n + 1), k * Nat.choose (2 * n) k = ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1)) :
   ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1) = ∑ x in range n, 2 * n * Nat.choose (2 * n - 1) x := by
  rw[sum_Ico_eq_sum_range]
  simp

theorem sum_range_succ_eq_sum_range_from_8_to_8(n : ℕ)(h01 : 0 < n + 1)(h1 : ∑ k in Ico 1 (n + 1), k * Nat.choose (2 * n) k = ∑ k in Ico 1 (n + 1), 2 * n * Nat.choose (2 * n - 1) (k - 1)) :
   ∑ k in range (n + 1 - 1), 2 * n * Nat.choose (2 * n - 1) (1 + k - 1) =
    ∑ x in range n, 2 * n * Nat.choose (2 * n - 1) x := by
  simp

