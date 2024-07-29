import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators


theorem sum_Ico_eq_sum_range_simp {n l : ℕ} {x : ℝ} : (choose n l) * ∑ k in Ico l (n+1), (choose (n-l) (k-l)) * x^k * (1 - x)^(n - k)
          = (choose n l) * ∑ k in range (n+1-l), (choose (n-l) k) * x^(l+k) * (1 - x)^(n-(l+k)) := by
  rw [sum_Ico_eq_sum_range]
  simp
