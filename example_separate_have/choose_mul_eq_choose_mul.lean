import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

theorem choose_mul_eq_choose_mul(hkn : k ≤ n) (hsk : 1 ≤ k) : choose n k * choose k 1 = choose n 1 * choose (n - 1) (k - 1)  := by rw[choose_mul hkn hsk]
