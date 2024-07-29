import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem cast_sum_choose_mul {n l : ℕ} {x : ℝ} : ∑ k in Ico l (n+1), (choose n k) * (choose k l) * x^k * (1 - x)^(n - k)
      = ∑ k in Ico l (n+1), (choose n l) * (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k) := by
  refine' sum_congr rfl fun k hk => _
  congr 2
  rw [mem_Ico] at hk
  rw [←cast_mul,←cast_mul]
  rw [choose_mul]
  linarith
  exact hk.left
