import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem sum_choose_mul_eq_choose_mul_sum {n l : ℕ} {x : ℝ} : ∑ k in Ico l (n+1), (choose n l) * (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k)
  = (choose n l)  * ∑ k in Ico l (n+1), (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k) := by
  rw [mul_sum]
  simp [mul_assoc]
