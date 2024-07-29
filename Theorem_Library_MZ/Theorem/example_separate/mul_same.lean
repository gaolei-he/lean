import Theorem.example_separate.choose_mul_eq_mul_sub

open Nat

theorem mul_same(hkn : k ≤ n)(hsk : 1 ≤ k) : choose n k * k * k  = n * k * choose (n - 1) (k - 1)  := by
      rw [choose_mul_eq_mul_sub (hkn) (hsk)]
      rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]


theorem mul_same_from_0_to_0(k n : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k)(gol:  n * choose (n - 1) (k - 1) * k = n * k * choose (n - 1) (k - 1)) :
   choose n k * k * k = n * k * choose (n - 1) (k - 1) := by
  rw [choose_mul_eq_mul_sub (hkn) (hsk)]
  apply gol

theorem mul_same_from_0_to_1(k n : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k) :
   choose n k * k * k = n * k * choose (n - 1) (k - 1) := by
  rw [choose_mul_eq_mul_sub (hkn) (hsk)]
  rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]

theorem mul_same_from_1_to_1(k n : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k) :
   n * choose (n - 1) (k - 1) * k = n * k * choose (n - 1) (k - 1) := by
  rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]

