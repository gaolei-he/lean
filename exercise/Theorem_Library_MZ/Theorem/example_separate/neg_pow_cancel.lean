import Theorem.example_separate.add_div_two

open Nat

open Finset

open BigOperators

theorem neg_pow_cancel : ∑ k in Ico 1 (n + 1), (-1 : ℤ) ^ k * n * (choose (n-1) (k-1)) =  ∑ k in Ico 1 (n + 1), (-1) ^ (k - 1) * (-1 : ℤ)* n * (choose (n-1) (k-1)) := by
    refine' sum_congr rfl fun y hy => _
    have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hnegy : (-1 : ℤ ) ^ y = (-1) ^ (y - 1 + 1)  := by
      rw[Nat.sub_add_cancel hy1]
    congr 2


theorem neg_pow_cancel_from_1_to_1(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  (-1 : ℝ) ^ y * ↑n * ↑(Nat.choose (n - 1) (y - 1)) = (-1 : ℝ) ^ (y - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (y - 1))) :
   (-1 : ℝ) ^ y * ↑n * ↑(Nat.choose (n - 1) (y - 1)) = (-1 : ℝ) ^ (y - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (y - 1)) := by
  have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
  apply gol

theorem neg_pow_cancel_from_1_to_2(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(gol:  (-1 : ℝ) ^ y * ↑n * ↑(Nat.choose (n - 1) (y - 1)) = (-1 : ℝ) ^ (y - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (y - 1))) :
   (-1 : ℝ) ^ y * ↑n * ↑(Nat.choose (n - 1) (y - 1)) = (-1 : ℝ) ^ (y - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (y - 1)) := by
  have hy1: 1 ≤ y := by exact (mem_Ico.1 hy).1
  have hnegy : (-1 : ℤ ) ^ y = (-1 : ℝ) ^ (y - 1 + 1)  := by
    rw[Nat.sub_add_cancel hy1]
  apply gol

theorem neg_pow_cancel_from_2_to_2(n y : ℕ)(hy : y ∈ Ico 1 (n + 1))(hy1 : 1 ≤ y)(gol:  (-1 : ℝ) ^ y * ↑n * ↑(Nat.choose (n - 1) (y - 1)) = (-1 : ℝ) ^ (y - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (y - 1))) :
   (-1 : ℝ) ^ y * ↑n * ↑(Nat.choose (n - 1) (y - 1)) = (-1 : ℝ) ^ (y - 1) * -1 * ↑n * ↑(Nat.choose (n - 1) (y - 1)) := by
  have hnegy : (-1 : ℤ ) ^ y = (-1 : ℝ) ^ (y - 1 + 1)  := by
    rw[Nat.sub_add_cancel hy1]
  apply gol

