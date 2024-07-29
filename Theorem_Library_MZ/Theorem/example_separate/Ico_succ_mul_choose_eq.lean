import Theorem.example_separate.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators

theorem Ico_succ_mul_choose_eq: ∑ k in Ico 1 (n+1), k * (choose (2 * n) k) = ∑ k in Ico 1 (n+1), (2 * n) * (choose (2*n - 1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
    have hkn: y ≤ 2 * n  := by linarith
    have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[choose_mul_eq_mul_sub' hkn hsk]


theorem Ico_succ_mul_choose_eq_from_1_to_1(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1)) :
   y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1) := by
  have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
  apply gol

theorem Ico_succ_mul_choose_eq_from_1_to_2(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1)) :
   y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1) := by
  have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hkn: y ≤ 2 * n  := by linarith
  apply gol

theorem Ico_succ_mul_choose_eq_from_1_to_3(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1)) :
   y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1) := by
  have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hkn: y ≤ 2 * n  := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_succ_mul_choose_eq_from_1_to_4(n y : ℕ)(hy : y ∈ Ico 1 (n + 1)) :
   y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1) := by
  have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hkn: y ≤ 2 * n  := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hkn hsk]

theorem Ico_succ_mul_choose_eq_from_2_to_2(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(gol:  y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1)) :
   y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1) := by
  have hkn: y ≤ 2 * n  := by linarith
  apply gol

theorem Ico_succ_mul_choose_eq_from_2_to_3(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(gol:  y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1)) :
   y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1) := by
  have hkn: y ≤ 2 * n  := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_succ_mul_choose_eq_from_2_to_4(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1) :
   y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1) := by
  have hkn: y ≤ 2 * n  := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hkn hsk]

theorem Ico_succ_mul_choose_eq_from_3_to_3(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n)(gol:  y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1)) :
   y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1) := by
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_succ_mul_choose_eq_from_3_to_4(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n) :
   y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1) := by
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[choose_mul_eq_mul_sub' hkn hsk]

theorem Ico_succ_mul_choose_eq_from_4_to_4(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n)(hsk : 1 ≤ y) :
   y * Nat.choose (2 * n) y = 2 * n * Nat.choose (2 * n - 1) (y - 1) := by
  rw[choose_mul_eq_mul_sub' hkn hsk]

