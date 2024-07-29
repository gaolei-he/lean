import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem simp_sub {n : ℕ} : (n*2^(2*n)) - ((n*2^(2*n) + 2^(2*n-1) - (2*n+1) * choose (2*n-1) n) : ℝ)
                = (2*n+1) * choose (2*n-1) n - 2^(2*n-1) := by
  rw [←add_sub, ←sub_sub, sub_self, ←sub_add, add_comm]
  congr 1
  simp
