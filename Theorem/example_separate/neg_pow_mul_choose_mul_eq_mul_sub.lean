import Theorem.example_separate.choose_mul_eq_mul_sub'

open Nat

open Finset

open BigOperators

theorem neg_pow_mul_choose_mul_eq_mul_sub:  ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * k * (choose n k) = ∑ k in Ico 1 (n + 1), (-1 : ℤ)^k * n * (choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hyn : y ≤ n := by
      have hy_succ: y < n + 1 := by exact (mem_Ico.1 hy).2
      linarith
    rw[mul_assoc, mul_assoc]
    congr 1
    rw[← cast_mul,← cast_mul]
    rw[choose_mul_eq_mul_sub' hyn hy1]


theorem neg_pow_mul_choose_mul_eq_mul_sub_from_1_to_1(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  (-1 : ℝ) ^ y * ↑y * ↑(Nat.choose n y) = (-1 : ℝ) ^ y * ↑n * ↑(Nat.choose (n - 1) (y - 1))) :
   (-1 : ℝ) ^ y * ↑y * ↑(Nat.choose n y) = (-1 : ℝ) ^ y * ↑n * ↑(Nat.choose (n - 1) (y - 1)) := by
  have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem neg_pow_mul_choose_mul_eq_mul_sub_from_3_to_3(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(hy1 : 1 ≤ y)(hyn : y ≤ n)(gol:  (-1 : ℝ) ^ y * (↑y * ↑(Nat.choose n y)) = (-1 : ℝ) ^ y * (↑n * ↑(Nat.choose (n - 1) (y - 1)))) :
   (-1 : ℝ) ^ y * ↑y * ↑(Nat.choose n y) = (-1 : ℝ) ^ y * ↑n * ↑(Nat.choose (n - 1) (y - 1)) := by
  rw[mul_assoc, mul_assoc]
  apply gol

theorem neg_pow_mul_choose_mul_eq_mul_sub_from_5_to_5(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(hy1 : 1 ≤ y)(hyn : y ≤ n)(gol:  ↑(y * Nat.choose n y) = ↑(n * Nat.choose (n - 1) (y - 1))) :
   ↑y * ↑(Nat.choose n y) = ↑n * ↑(Nat.choose (n - 1) (y - 1)) := by
  rw[← cast_mul,← cast_mul]
  apply gol

theorem neg_pow_mul_choose_mul_eq_mul_sub_from_5_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(hy1 : 1 ≤ y)(hyn : y ≤ n) :
   ↑y * ↑(Nat.choose n y) = ↑n * ↑(Nat.choose (n - 1) (y - 1)) := by
  rw[← cast_mul,← cast_mul]
  rw[choose_mul_eq_mul_sub' hyn hy1]

theorem neg_pow_mul_choose_mul_eq_mul_sub_from_6_to_6(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(hy1 : 1 ≤ y)(hyn : y ≤ n) :
   ↑(y * Nat.choose n y) = ↑(n * Nat.choose (n - 1) (y - 1)) := by
  rw[choose_mul_eq_mul_sub' hyn hy1]

