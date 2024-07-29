import AdaLean.choose_mul_eq_mul_sub
import AdaLean.mul_same

open Nat

theorem choose_mul_pow_eq_mul(hkn : k ≤ n)(hsk : 1 ≤ k): choose n k * (k ^ 2)  = n * k * choose (n - 1) (k - 1)  := by
  rw[pow_two]
  rw[mul_same hkn hsk]
