import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Lean4Repl

open Nat
open Finset
open BigOperators

theorem sum_pow_mul_eq_pow_mul_sum {n l : ℕ} {x : ℝ} : (choose n l) * ∑ k in range (n+1-l), x^l * x^k * (choose (n-l) k) * (1 - x)^(n-(l+k))
                          = (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^(n-(l+k)) := by lean_repl sorry
  rw [mul_assoc]
  repeat rw [mul_sum]
  simp [mul_assoc]
