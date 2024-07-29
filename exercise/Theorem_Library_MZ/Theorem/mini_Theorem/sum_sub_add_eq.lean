import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem sum_sub_add_eq {n l : ℕ} {x : ℝ} : (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^(n-(l+k))
                          = (choose n l) * x^l * ∑ k in range (n+1-l), x^k * (choose (n-l) k) * (1 - x)^((n-l)-k) := by
  congr 1
  refine' sum_congr rfl fun k hk => _
  congr 2
  exact sub_add_eq n l k
