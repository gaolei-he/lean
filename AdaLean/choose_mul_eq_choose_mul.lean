import Mathlib.Data.Nat.Choose.Sum

open Nat

theorem choose_mul_eq_choose_mul(hkn : k ≤ n) (hsk : 1 ≤ k) : choose k 1  * choose n k= choose n 1 * choose (n - 1) (k - 1)  := by
  rw[mul_comm]
  rw[choose_mul hkn hsk]
