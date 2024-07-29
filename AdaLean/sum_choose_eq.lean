import Mathlib.Data.Nat.Choose.Sum


open Nat

open Finset

open BigOperators


theorem sum_choose_eq: ∑ k in Ico 0 n, Nat.choose (2 * n) k = ∑ k in Ico 0 n, Nat.choose (2 * n) (2 * n - k) := by
    refine' sum_congr rfl fun y hy ↦ _
    have yn : y < n := by exact (mem_Ico.1 hy).2
    have y2n : y ≤ 2 * n := by linarith
    rw[← choose_symm y2n]
