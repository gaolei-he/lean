import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Real.Basic

open Nat

open Finset

open BigOperators

variable {R : Type*}

example{n k m : ℕ} (hk : k ≤ n) (hm : m ≤ n) (hkm : m ≤ k) : (∑ k in Icc 0 n,  (choose n k) * (descFactorial (k + 1) m)) = (∑ k in Icc m n, (descFactorial (n + 1) m) * choose (n - m) (k - m)) := by
  have h2(k:ℕ) : (choose n k) * (descFactorial (k + 1) m) = (descFactorial (n + 1) m) * choose (n - m) (k - m) := by
    sorry
  refine' sum_congr _ fun y _ => h2 (y)
  have h3 : (∑ k in Icc m n, descFactorial n m * Nat.choose (n - m) (k - m)) = descFactorial n m * (∑ k in Icc m n, Nat.choose (n - m) (k - m)) := by
    rw[mul_sum]

example: 2^(n-m)= (∑ k in range (n - m), Nat.choose n k) := by
  rw[← sum_range_choose]
  rw[range_eq_Ico]
  rw[sum_Ico_succ_top]
  simp

theorem o3 : (∑ k in range (n + 1 - m), Nat.choose (n-m) (m + k - m)) = (∑ k in range (n + 1 - m), Nat.choose (n-m) k) := by
  refine' sum_congr rfl fun y hy => _
  rw[Nat.add_sub_cancel_left]
