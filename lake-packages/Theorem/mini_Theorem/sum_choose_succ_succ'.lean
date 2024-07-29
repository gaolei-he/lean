import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat
open Finset
open BigOperators

theorem sum_choose_succ_succ' {n : ℕ} : ∑ k in Ico 1 (n + 1), k * choose (2*n+1) k
                  = ∑ k in Ico 1 (n + 1), k * (choose (2*n) k + choose (2*n) (k-1)) := by
  refine' sum_congr rfl fun k hk => _
  congr 1
  have : k = k-1+1 := by
    rw [Nat.sub_add_cancel]
    rw [mem_Ico] at hk
    exact hk.left
  rw [this, choose_succ_succ' (2*n) (k-1), ←this, add_comm]
