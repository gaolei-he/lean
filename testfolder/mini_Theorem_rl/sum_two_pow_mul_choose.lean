import Mathlib.Data.Nat.Choose.Sum
import Lean4Repl
open Nat

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem sum_two_pow_mul_choose {n : ℕ} : ∑ k in range (n+1), 2^k * choose n k = 3^n := by lean_repl sorry
  rw[← two_add_one_eq_three]
  rw[add_pow]
  simp
