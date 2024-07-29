import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem sum_choose_mul_pow_comm {n l : ℕ} {x : ℝ} (h : l ≤ n) : (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^((n-l)-k)
                          = (choose n l) * x^l * ∑ k in range (n-l+1), x^k * (1 - x)^((n-l)-k) * (choose (n-l) k) := by
  have : n+1-l = n-l+1 := by rw [succ_sub h]
  rw [this]
  congr 1
  refine' sum_congr rfl fun k hk => _
  rw [mul_assoc,mul_assoc]
  congr 1
  rw [mul_comm]
