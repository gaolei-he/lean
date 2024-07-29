import Theorem.example_separate.mul_choose_sub

open Nat

open Finset

open BigOperators

theorem ico_mul_choose_sub(hn0 : 0 < n) : ∑ l in Ico 1 n ,l * choose (n-1) l  = ∑ l in Ico 1 n, (n - 1) * choose (n-2) (l-1) := by
  refine' sum_congr rfl fun y hy ↦ _
  have hyn : y < n := by exact (mem_Ico.1 hy).2
  have lt_eq_le_sub : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[mul_choose_sub hy_sub_1 hy1]


theorem ico_mul_choose_sub_from_1_to_1(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(gol:  y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1)) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have hyn : y < n := by exact (mem_Ico.1 hy).2
  apply gol

theorem ico_mul_choose_sub_from_1_to_2(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(gol:  y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1)) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have hyn : y < n := by exact (mem_Ico.1 hy).2
  have lt_eq_le_sub : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
  apply gol

theorem ico_mul_choose_sub_from_1_to_3(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(gol:  y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1)) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have hyn : y < n := by exact (mem_Ico.1 hy).2
  have lt_eq_le_sub : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  apply gol

theorem ico_mul_choose_sub_from_1_to_4(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(gol:  y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1)) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have hyn : y < n := by exact (mem_Ico.1 hy).2
  have lt_eq_le_sub : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem ico_mul_choose_sub_from_1_to_5(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have hyn : y < n := by exact (mem_Ico.1 hy).2
  have lt_eq_le_sub : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[mul_choose_sub hy_sub_1 hy1]

theorem ico_mul_choose_sub_from_2_to_2(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(hyn : y < n)(gol:  y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1)) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have lt_eq_le_sub : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
  apply gol

theorem ico_mul_choose_sub_from_2_to_3(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(hyn : y < n)(gol:  y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1)) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have lt_eq_le_sub : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  apply gol

theorem ico_mul_choose_sub_from_2_to_4(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(hyn : y < n)(gol:  y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1)) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have lt_eq_le_sub : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem ico_mul_choose_sub_from_2_to_5(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(hyn : y < n) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have lt_eq_le_sub : y < n → y ≤ n - 1 := by
    rw[Nat.lt_iff_le_pred hn0]
    intro a
    exact a
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[mul_choose_sub hy_sub_1 hy1]

theorem ico_mul_choose_sub_from_3_to_3(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(hyn : y < n)(lt_eq_le_sub : y < n → y ≤ n - 1)(gol:  y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1)) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  apply gol

theorem ico_mul_choose_sub_from_3_to_4(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(hyn : y < n)(lt_eq_le_sub : y < n → y ≤ n - 1)(gol:  y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1)) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem ico_mul_choose_sub_from_3_to_5(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(hyn : y < n)(lt_eq_le_sub : y < n → y ≤ n - 1) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have hy_sub_1 : y ≤ n - 1 := by
    exact lt_eq_le_sub hyn
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[mul_choose_sub hy_sub_1 hy1]

theorem ico_mul_choose_sub_from_4_to_4(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(hyn : y < n)(lt_eq_le_sub : y < n → y ≤ n - 1)(hy_sub_1 : y ≤ n - 1)(gol:  y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1)) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem ico_mul_choose_sub_from_4_to_5(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(hyn : y < n)(lt_eq_le_sub : y < n → y ≤ n - 1)(hy_sub_1 : y ≤ n - 1) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[mul_choose_sub hy_sub_1 hy1]

theorem ico_mul_choose_sub_from_5_to_5(n : ℕ)(hn0 : 0 < n)(y : ℕ)(hy : y ∈ Ico 1 n)(hyn : y < n)(lt_eq_le_sub : y < n → y ≤ n - 1)(hy_sub_1 : y ≤ n - 1)(hy1 : 1 ≤ y) :
   y * Nat.choose (n - 1) y = (n - 1) * Nat.choose (n - 2) (y - 1) := by
  rw[mul_choose_sub hy_sub_1 hy1]

