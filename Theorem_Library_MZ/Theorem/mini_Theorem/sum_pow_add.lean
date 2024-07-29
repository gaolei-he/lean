import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem sum_pow_add {n l : ℕ} {x : ℝ} : (choose n l) * ∑ k in range (n+1-l), x^(l+k) * (choose (n-l) k) * (1 - x)^(n-(l+k))
        = (choose n l) * ∑ k in range (n+1-l), x^l * x^k * (choose (n-l) k) * (1 - x)^(n-(l+k)) := by
  congr 1
  refine' sum_congr rfl fun k hk => _
  rw [pow_add]
