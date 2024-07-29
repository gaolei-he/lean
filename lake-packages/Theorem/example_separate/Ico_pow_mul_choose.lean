import Theorem.example_separate.pow_mul_choose

open Nat

open Finset

open BigOperators

theorem Ico_pow_mul_choose :   --sum41
  ∑ k in Ico 1 (n + 1), k ^ 2 * choose n k = n * ∑ k in Ico 1 (n + 1), k * choose (n-1) (k-1)  := by
    rw[mul_sum]
    refine' sum_congr rfl fun y hy ↦ _
    have yn_succ : y < n + 1 := by exact (mem_Ico.1 hy).2
    have hyn : y ≤ n := by
      exact Nat.le_of_lt_succ yn_succ
    have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
    rw[pow_mul_choose (hyn) (hy1)]
    rw[mul_assoc]


theorem Ico_pow_mul_choose_from_0_to_0(n : ℕ)(gol:  ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = ∑ x in Ico 1 (n + 1), n * (x * Nat.choose (n - 1) (x - 1))) :
   ∑ k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * ∑ k in Ico 1 (n + 1), k * Nat.choose (n - 1) (k - 1) := by
  rw[mul_sum]
  apply gol

theorem Ico_pow_mul_choose_from_2_to_2(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1))) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have yn_succ : y < n + 1 := by exact (mem_Ico.1 hy).2
  apply gol

theorem Ico_pow_mul_choose_from_2_to_3(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1))) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have yn_succ : y < n + 1 := by exact (mem_Ico.1 hy).2
  have hyn : y ≤ n := by
    exact Nat.le_of_lt_succ yn_succ
  apply gol

theorem Ico_pow_mul_choose_from_2_to_4(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1))) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have yn_succ : y < n + 1 := by exact (mem_Ico.1 hy).2
  have hyn : y ≤ n := by
    exact Nat.le_of_lt_succ yn_succ
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_pow_mul_choose_from_2_to_5(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  n * y * Nat.choose (n - 1) (y - 1) = n * (y * Nat.choose (n - 1) (y - 1))) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have yn_succ : y < n + 1 := by exact (mem_Ico.1 hy).2
  have hyn : y ≤ n := by
    exact Nat.le_of_lt_succ yn_succ
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[pow_mul_choose (hyn) (hy1)]
  apply gol

theorem Ico_pow_mul_choose_from_2_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1)) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have yn_succ : y < n + 1 := by exact (mem_Ico.1 hy).2
  have hyn : y ≤ n := by
    exact Nat.le_of_lt_succ yn_succ
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[pow_mul_choose (hyn) (hy1)]
  rw[mul_assoc]

theorem Ico_pow_mul_choose_from_3_to_3(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(yn_succ : y < n + 1)(gol:  y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1))) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have hyn : y ≤ n := by
    exact Nat.le_of_lt_succ yn_succ
  apply gol

theorem Ico_pow_mul_choose_from_3_to_4(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(yn_succ : y < n + 1)(gol:  y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1))) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have hyn : y ≤ n := by
    exact Nat.le_of_lt_succ yn_succ
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_pow_mul_choose_from_3_to_5(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(yn_succ : y < n + 1)(gol:  n * y * Nat.choose (n - 1) (y - 1) = n * (y * Nat.choose (n - 1) (y - 1))) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have hyn : y ≤ n := by
    exact Nat.le_of_lt_succ yn_succ
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[pow_mul_choose (hyn) (hy1)]
  apply gol

theorem Ico_pow_mul_choose_from_3_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(yn_succ : y < n + 1) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have hyn : y ≤ n := by
    exact Nat.le_of_lt_succ yn_succ
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[pow_mul_choose (hyn) (hy1)]
  rw[mul_assoc]

theorem Ico_pow_mul_choose_from_4_to_4(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(yn_succ : y < n + 1)(hyn : y ≤ n)(gol:  y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1))) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem Ico_pow_mul_choose_from_4_to_5(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(yn_succ : y < n + 1)(hyn : y ≤ n)(gol:  n * y * Nat.choose (n - 1) (y - 1) = n * (y * Nat.choose (n - 1) (y - 1))) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[pow_mul_choose (hyn) (hy1)]
  apply gol

theorem Ico_pow_mul_choose_from_4_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(yn_succ : y < n + 1)(hyn : y ≤ n) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  have hy1 : 1 ≤ y := by exact (mem_Ico.1 hy).1
  rw[pow_mul_choose (hyn) (hy1)]
  rw[mul_assoc]

theorem Ico_pow_mul_choose_from_5_to_5(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(yn_succ : y < n + 1)(hyn : y ≤ n)(hy1 : 1 ≤ y)(gol:  n * y * Nat.choose (n - 1) (y - 1) = n * (y * Nat.choose (n - 1) (y - 1))) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  rw[pow_mul_choose (hyn) (hy1)]
  apply gol

theorem Ico_pow_mul_choose_from_5_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(yn_succ : y < n + 1)(hyn : y ≤ n)(hy1 : 1 ≤ y) :
   y ^ 2 * Nat.choose n y = n * (y * Nat.choose (n - 1) (y - 1)) := by
  rw[pow_mul_choose (hyn) (hy1)]
  rw[mul_assoc]

theorem Ico_pow_mul_choose_from_6_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(yn_succ : y < n + 1)(hyn : y ≤ n)(hy1 : 1 ≤ y) :
   n * y * Nat.choose (n - 1) (y - 1) = n * (y * Nat.choose (n - 1) (y - 1)) := by
  rw[mul_assoc]

