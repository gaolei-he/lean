import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators


def delta (m n : ℕ) : ℕ :=
  if m = n then 1 else 0

theorem alternating_sum_choose_mul { m n : ℕ } (h : m ≤ n) :
  ( ∑ k in Ico m (n + 1), (-1 : ℤ) ^ k * (choose n k) * (choose k m) ) = (-1) ^ m * delta m n := by
  by_cases h_eq : m = n
  . rw [h_eq]
    simp [delta]
  . rw [delta]
    simp [h_eq]
    have h1 : ∀ m n i: ℕ, i ∈ Ico m (n+1) →
      (-1 : ℤ) ^ i * (choose n i) * (choose i m) = (-1 : ℤ) ^ i * (choose n m * choose (n-m) (i-m)) := by
      intro m n i hi
      have h2 : i ≤ n := Nat.le_of_lt_succ (mem_Ico.mp hi).right
      have h3 : m ≤ i := (mem_Ico.mp hi).left
      simp_rw [mul_assoc, ←cast_mul]
      congr 1
      rw [choose_mul h2 h3]
    rw [sum_congr rfl (h1 m n)]
    rw [sum_Ico_eq_sum_range]
    rw [add_comm, add_tsub_assoc_of_le h, add_comm]
    simp [pow_add,mul_assoc]
    rw [←mul_sum]
    simp_rw [←cast_mul, ←cast_comm, cast_mul, mul_assoc, ←mul_sum, ←mul_assoc, cast_comm]
    have h4 : 0 < n - m := tsub_pos_of_lt (lt_of_le_of_ne h h_eq)
    rw [pos_iff_ne_zero] at h4
    rw [Int.alternating_sum_range_choose_of_ne h4]
    simp


