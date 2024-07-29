import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Real.Basic


open Nat


theorem Real_choose_eq_choose_add(h1:1 ≤ n)(h2:1 ≤ k) : (choose n k : ℝ) = (choose (n-1) k : ℝ)  + (choose (n-1) (k-1): ℝ) := by
  have choose_eq_choose_sub_add :  (choose n k : ℝ) = ((choose (n - 1 + 1) (k - 1 + 1)) : ℝ)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  have choose_sub_eq_choose_sub_add : ((choose (n - 1) k) : ℝ) = ((choose (n - 1) (k - 1 + 1)) : ℝ ):= by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]
  rw[add_comm]
  simp
