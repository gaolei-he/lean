import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem sum_two_pow_mul_choose {n : ℕ} : ∑ k in range (n+1), 2^k * choose n k = 3^n := by
  have : ∑ m in range (n + 1), 2 ^ m * 1 ^ (n - m) * ↑(Nat.choose n m) = (2 + 1) ^ n :=
    (add_pow _ _ _).symm
  simp at this
  assumption


theorem sum_two_pow_mul_choose_from_0_to_0(n : ℕ)(gol:  ∑ k in range (n + 1), 2 ^ k * Nat.choose n k = 3 ^ n) :
   ∑ k in range (n + 1), 2 ^ k * Nat.choose n k = 3 ^ n := by
  have : ∑ m in range (n + 1), 2 ^ m * 1 ^ (n - m) * ↑(Nat.choose n m) = (2 + 1) ^ n :=
    (add_pow _ _ _).symm
  apply gol

theorem sum_two_pow_mul_choose_from_0_to_1(n : ℕ)(gol:  ∑ k in range (n + 1), 2 ^ k * Nat.choose n k = 3 ^ n) :
   ∑ k in range (n + 1), 2 ^ k * Nat.choose n k = 3 ^ n := by
  have : ∑ m in range (n + 1), 2 ^ m * 1 ^ (n - m) * ↑(Nat.choose n m) = (2 + 1) ^ n :=
    (add_pow _ _ _).symm
  simp at this
  apply gol

theorem sum_two_pow_mul_choose_from_0_to_2(n : ℕ) :
   ∑ k in range (n + 1), 2 ^ k * Nat.choose n k = 3 ^ n := by
  have : ∑ m in range (n + 1), 2 ^ m * 1 ^ (n - m) * ↑(Nat.choose n m) = (2 + 1) ^ n :=
    (add_pow _ _ _).symm
  simp at this
  assumption

theorem sum_two_pow_mul_choose_from_1_to_1(n : ℕ)(this : ∑ m in range (n + 1), 2 ^ m * 1 ^ (n - m) * Nat.choose n m = (2 + 1) ^ n)(gol:  ∑ k in range (n + 1), 2 ^ k * Nat.choose n k = 3 ^ n) :
   ∑ k in range (n + 1), 2 ^ k * Nat.choose n k = 3 ^ n := by
  simp at this
  apply gol

theorem sum_two_pow_mul_choose_from_1_to_2(n : ℕ)(this : ∑ m in range (n + 1), 2 ^ m * 1 ^ (n - m) * Nat.choose n m = (2 + 1) ^ n) :
   ∑ k in range (n + 1), 2 ^ k * Nat.choose n k = 3 ^ n := by
  simp at this
  assumption

theorem sum_two_pow_mul_choose_from_2_to_2(n : ℕ)(this : ∑ x in range (n + 1), 2 ^ x * Nat.choose n x = (2 + 1) ^ n) :
   ∑ k in range (n + 1), 2 ^ k * Nat.choose n k = 3 ^ n := by
  assumption

