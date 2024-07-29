import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem mul_mul_one_pow {n l : ℕ} {x : ℝ} : (choose n l) * x^l * (1)^(n-l) = (choose n l) * x^l := by
  rw [one_pow]
  simp
