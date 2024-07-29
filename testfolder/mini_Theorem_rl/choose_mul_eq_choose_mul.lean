import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl

open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem choose_mul_eq_choose_mul(hkn : k ≤ n) (hsk : 1 ≤ k) : choose n k * choose k 1 = choose n 1 * choose (n - 1) (k - 1)  := by lean_repl sorry
  rw[choose_mul]
