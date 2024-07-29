import Mathlib.Data.Nat.Choose.Sum


open Nat

open Finset

open BigOperators


theorem sum_choose_eq: ∑ k in Ico 0 n, Nat.choose (2 * n) k = ∑ k in Ico 0 n, Nat.choose (2 * n) (2 * n - k) := by
    refine' sum_congr rfl fun y hy ↦ _
    have yn : y < n := by exact (mem_Ico.1 hy).2
    have y2n : y ≤ 2 * n := by linarith
    rw[← choose_symm y2n]


theorem sum_choose_eq_from_1_to_1(n y : ℕ)(hy : y ∈ Ico 0 n)(gol:  Nat.choose (2 * n) y = Nat.choose (2 * n) (2 * n - y)) :
   Nat.choose (2 * n) y = Nat.choose (2 * n) (2 * n - y) := by
  have yn : y < n := by exact (mem_Ico.1 hy).2
  apply gol

theorem sum_choose_eq_from_1_to_2(n y : ℕ)(hy : y ∈ Ico 0 n)(gol:  Nat.choose (2 * n) y = Nat.choose (2 * n) (2 * n - y)) :
   Nat.choose (2 * n) y = Nat.choose (2 * n) (2 * n - y) := by
  have yn : y < n := by exact (mem_Ico.1 hy).2
  have y2n : y ≤ 2 * n := by linarith
  apply gol

theorem sum_choose_eq_from_1_to_3(n y : ℕ)(hy : y ∈ Ico 0 n) :
   Nat.choose (2 * n) y = Nat.choose (2 * n) (2 * n - y) := by
  have yn : y < n := by exact (mem_Ico.1 hy).2
  have y2n : y ≤ 2 * n := by linarith
  rw[← choose_symm y2n]

theorem sum_choose_eq_from_2_to_2(n y : ℕ)(hy : y ∈ Ico 0 n)(yn : y < n)(gol:  Nat.choose (2 * n) y = Nat.choose (2 * n) (2 * n - y)) :
   Nat.choose (2 * n) y = Nat.choose (2 * n) (2 * n - y) := by
  have y2n : y ≤ 2 * n := by linarith
  apply gol

theorem sum_choose_eq_from_2_to_3(n y : ℕ)(hy : y ∈ Ico 0 n)(yn : y < n) :
   Nat.choose (2 * n) y = Nat.choose (2 * n) (2 * n - y) := by
  have y2n : y ≤ 2 * n := by linarith
  rw[← choose_symm y2n]

theorem sum_choose_eq_from_3_to_3(n y : ℕ)(hy : y ∈ Ico 0 n)(yn : y < n)(y2n : y ≤ 2 * n) :
   Nat.choose (2 * n) y = Nat.choose (2 * n) (2 * n - y) := by
  rw[← choose_symm y2n]

