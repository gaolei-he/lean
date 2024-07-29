import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat

open Finset

open BigOperators

theorem sum_assoc : ∑ k in Ico 1 (2 * m), (-1 : ℝ) * (-1 : ℝ) ^ (k - 1) / Nat.choose (2 * m) k = ∑ k in Ico 1 (2 * m), (-1 : ℝ) * ((-1 : ℝ) ^ (k - 1) / Nat.choose (2 * m) k) := by  --用mul_div结合律，方便后续提取-1
  refine' sum_congr rfl fun y _ => _
  rw[← mul_div]


theorem sum_assoc_from_1_to_1(m y : ℕ)(x✝ : y ∈ Ico 1 (2 * m)) :
   -1 * (-1 : ℝ) ^ (y - 1) / ↑(Nat.choose (2 * m) y) = -1 * ((-1 : ℝ) ^ (y - 1) / ↑(Nat.choose (2 * m) y)) := by
  rw[← mul_div]

