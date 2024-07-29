import Mathlib.Data.Real.Basic
import Theorem.example_separate.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators

theorem Ico_choose: ∑ k in Ico 1 (n+1), k * ((choose (2*n + 1) k):ℝ) = ∑ k in Ico 1 (n+1), (2 * n + 1) * ((choose (2*n) (k-1)):ℝ) := by
    refine' sum_congr rfl fun y hy => _
    have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
    have hkn: y ≤ 2 * n + 1 := by linarith
    have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[← cast_mul]
    rw[choose_mul_eq_mul_sub' hkn hsk]
    simp


theorem Ico_choose_from_1_to_1(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
  apply gol

theorem Ico_choose_from_1_to_2(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hkn: y ≤ 2 * n + 1 := by linarith
  apply gol

theorem Ico_choose_from_1_to_3(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hkn: y ≤ 2 * n + 1 := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_choose_from_1_to_4(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  ↑(y * Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hkn: y ≤ 2 * n + 1 := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[← cast_mul]
  apply gol

theorem Ico_choose_from_1_to_5(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  ↑((2 * n + 1) * Nat.choose (2 * n + 1 - 1) (y - 1)) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hkn: y ≤ 2 * n + 1 := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[← cast_mul]
  rw[choose_mul_eq_mul_sub' hkn hsk]
  apply gol

theorem Ico_choose_from_1_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1)) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have h1n: y < n + 1 := by exact (mem_Ico.1 hy).2
  have hkn: y ≤ 2 * n + 1 := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[← cast_mul]
  rw[choose_mul_eq_mul_sub' hkn hsk]
  simp

theorem Ico_choose_from_2_to_2(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(gol:  ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have hkn: y ≤ 2 * n + 1 := by linarith
  apply gol

theorem Ico_choose_from_2_to_3(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(gol:  ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have hkn: y ≤ 2 * n + 1 := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_choose_from_2_to_4(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(gol:  ↑(y * Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have hkn: y ≤ 2 * n + 1 := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[← cast_mul]
  apply gol

theorem Ico_choose_from_2_to_5(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(gol:  ↑((2 * n + 1) * Nat.choose (2 * n + 1 - 1) (y - 1)) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have hkn: y ≤ 2 * n + 1 := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[← cast_mul]
  rw[choose_mul_eq_mul_sub' hkn hsk]
  apply gol

theorem Ico_choose_from_2_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have hkn: y ≤ 2 * n + 1 := by linarith
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[← cast_mul]
  rw[choose_mul_eq_mul_sub' hkn hsk]
  simp

theorem Ico_choose_from_3_to_3(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n + 1)(gol:  ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_choose_from_3_to_4(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n + 1)(gol:  ↑(y * Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[← cast_mul]
  apply gol

theorem Ico_choose_from_3_to_5(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n + 1)(gol:  ↑((2 * n + 1) * Nat.choose (2 * n + 1 - 1) (y - 1)) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[← cast_mul]
  rw[choose_mul_eq_mul_sub' hkn hsk]
  apply gol

theorem Ico_choose_from_3_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n + 1) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  have hsk: 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[← cast_mul]
  rw[choose_mul_eq_mul_sub' hkn hsk]
  simp

theorem Ico_choose_from_4_to_4(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n + 1)(hsk : 1 ≤ y)(gol:  ↑(y * Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  rw[← cast_mul]
  apply gol

theorem Ico_choose_from_4_to_5(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n + 1)(hsk : 1 ≤ y)(gol:  ↑((2 * n + 1) * Nat.choose (2 * n + 1 - 1) (y - 1)) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  rw[← cast_mul]
  rw[choose_mul_eq_mul_sub' hkn hsk]
  apply gol

theorem Ico_choose_from_4_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n + 1)(hsk : 1 ≤ y) :
   ↑y * ↑(Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  rw[← cast_mul]
  rw[choose_mul_eq_mul_sub' hkn hsk]
  simp

theorem Ico_choose_from_5_to_5(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n + 1)(hsk : 1 ≤ y)(gol:  ↑((2 * n + 1) * Nat.choose (2 * n + 1 - 1) (y - 1)) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1))) :
   ↑(y * Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  rw[choose_mul_eq_mul_sub' hkn hsk]
  apply gol

theorem Ico_choose_from_5_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n + 1)(hsk : 1 ≤ y) :
   ↑(y * Nat.choose (2 * n + 1) y) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  rw[choose_mul_eq_mul_sub' hkn hsk]
  simp

theorem Ico_choose_from_6_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(h1n : y < n + 1)(hkn : y ≤ 2 * n + 1)(hsk : 1 ≤ y) :
   ↑((2 * n + 1) * Nat.choose (2 * n + 1 - 1) (y - 1)) = (2 * ↑n + 1) * ↑(Nat.choose (2 * n) (y - 1)) := by
  simp

