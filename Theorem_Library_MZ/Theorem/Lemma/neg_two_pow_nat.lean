import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic



open Nat

open Finset

open BigOperators

lemma neg_two_pow_nat {x: ℕ} : (-2:ℝ) ^ x = (-1) ^ x * 2 ^ x := by
    rw [←mul_pow]
    congr
    simp
