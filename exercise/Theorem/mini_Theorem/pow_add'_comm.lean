import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic



open Nat
open Finset
open BigOperators


theorem pow_add'_comm {n : ℕ} (h : 1 ≤ n) : 2*(n:ℝ)*2^(2*n-1) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n
                  = n*2^(2*n) + 2^(2*n-1) + ((1/2) : ℝ) * choose (2*n) n - (n+1) * choose (2*n) n := by
  congr 3
  rw [←cast_comm, mul_assoc]
  congr 1
  have : 2*n = 2*n-1+1 := by
    have : 1 ≤ 2*n := by rw [two_mul]; linarith
    rw [Nat.sub_add_cancel this]
  rw [this, pow_add, ←this, pow_one, mul_comm]
