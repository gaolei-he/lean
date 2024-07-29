import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators


theorem mul_add_comm_simp {n : ℕ} : n * ((2^(2*n-1)) + (((1/2):ℝ) * choose (2*n) n)) - ((n * 2^(2*n-1)) :ℕ)
                = n * (((1/2):ℝ) * choose (2*n) n) := by
  rw [mul_add]
  rw [add_comm]
  simp
