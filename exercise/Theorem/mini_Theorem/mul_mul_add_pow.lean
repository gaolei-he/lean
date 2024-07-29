import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem mul_mul_add_pow {n l : ℕ} {x : ℝ} : (choose n l) * x^l * ∑ k in range (n-l+1), x^k * (1 - x)^((n-l)-k) * (choose (n-l) k)
                          = (choose n l) * x^l * (x + (1-x))^(n-l) := by rw [←add_pow (x:ℝ) (1-x) (n-l)]
