import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem mul_mul_pow_add_sub {n l : ℕ} {x : ℝ} : (choose n l) * x^l * (x + (1-x))^(n-l) = (choose n l) * x^l * (1)^(n-l) := by
  rw [add_sub]
  congr 2
  rw [add_sub_right_comm x 1 x, sub_self]
  simp
