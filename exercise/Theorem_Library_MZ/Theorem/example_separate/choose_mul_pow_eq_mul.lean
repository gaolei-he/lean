import Theorem.example_separate.choose_mul_eq_mul_sub

open Nat

theorem choose_mul_pow_eq_mul(hkn : k ≤ n)(hsk : 1 ≤ k): choose n k * (k ^ 2)  = n * k * choose (n - 1) (k - 1)  := by
  have mul_same : choose n k * k * k  = n * k * choose (n - 1) (k - 1)  := by
      rw [choose_mul_eq_mul_sub (hkn) (hsk)]
      rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]
  rw[Nat.mul_assoc] at mul_same
  rw[pow_two, mul_same]


theorem choose_mul_pow_eq_mul_from_0_to_0(k n : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k)(gol:  choose n k * k ^ 2 = n * k * choose (n - 1) (k - 1)) :
   choose n k * k ^ 2 = n * k * choose (n - 1) (k - 1) := by
  have mul_same : choose n k * k * k  = n * k * choose (n - 1) (k - 1)  := by
      rw [choose_mul_eq_mul_sub (hkn) (hsk)]
      rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]
  apply gol

theorem choose_mul_pow_eq_mul_from_0_to_1(k n : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k)(gol:  choose n k * k ^ 2 = n * k * choose (n - 1) (k - 1)) :
   choose n k * k ^ 2 = n * k * choose (n - 1) (k - 1) := by
  have mul_same : choose n k * k * k  = n * k * choose (n - 1) (k - 1)  := by
      rw [choose_mul_eq_mul_sub (hkn) (hsk)]
      rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]
  rw[Nat.mul_assoc] at mul_same
  apply gol

theorem choose_mul_pow_eq_mul_from_0_to_2(k n : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k) :
   choose n k * k ^ 2 = n * k * choose (n - 1) (k - 1) := by
  have mul_same : choose n k * k * k  = n * k * choose (n - 1) (k - 1)  := by
      rw [choose_mul_eq_mul_sub (hkn) (hsk)]
      rw [Nat.mul_assoc ,Nat.mul_comm (choose (n - 1) (k - 1)) k, Nat.mul_assoc]
  rw[Nat.mul_assoc] at mul_same
  rw[pow_two, mul_same]

theorem choose_mul_pow_eq_mul_from_1_to_1(k n : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k)(mul_same : choose n k * k * k = n * k * choose (n - 1) (k - 1))(gol:  choose n k * k ^ 2 = n * k * choose (n - 1) (k - 1)) :
   choose n k * k ^ 2 = n * k * choose (n - 1) (k - 1) := by
  rw[Nat.mul_assoc] at mul_same
  apply gol

theorem choose_mul_pow_eq_mul_from_1_to_2(k n : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k)(mul_same : choose n k * k * k = n * k * choose (n - 1) (k - 1)) :
   choose n k * k ^ 2 = n * k * choose (n - 1) (k - 1) := by
  rw[Nat.mul_assoc] at mul_same
  rw[pow_two, mul_same]

theorem choose_mul_pow_eq_mul_from_2_to_2(k n : ℕ)(hkn : k ≤ n)(hsk : 1 ≤ k)(mul_same : choose n k * (k * k) = n * k * choose (n - 1) (k - 1)) :
   choose n k * k ^ 2 = n * k * choose (n - 1) (k - 1) := by
  rw[pow_two, mul_same]

