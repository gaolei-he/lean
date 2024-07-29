import Mathlib.Data.Nat.Choose.Sum

open Nat

theorem choose_mul_eq_mul_sub {n k : ℕ} (hkn : k ≤ n) (hsk : 1 ≤ k) :  -- 定理1.3
    choose n k * k  = n * choose (n - 1) (k - 1) := by
      have choose_mul_eq_choose_mul : choose n k * choose k 1 = choose n 1 * choose (n - 1) (k - 1)  := by rw[choose_mul hkn hsk]
      rw[choose_one_right, choose_one_right] at choose_mul_eq_choose_mul
      rw[choose_mul_eq_choose_mul]
