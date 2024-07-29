-- import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem choose_eq_factorial_div_two {n k : ℕ} (hk : 2*k ≤ n) :
    choose n (2*k) = n ! / ((2*k) ! * (n - 2*k)!) := by
    rw [choose_eq_factorial_div_factorial hk]
