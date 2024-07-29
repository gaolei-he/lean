import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic


open Nat

open Finset

open BigOperators


theorem neg_pow_div_choose : ∑ k in Ico 1 (2 * m), (-1 : ℝ) ^ k / Nat.choose (2 * m) k = ∑ k in Ico 1 (2 * m), ((-1) * (-1 : ℝ) ^ (k - 1) ) / Nat.choose (2 * m) k := by
    refine' sum_congr rfl fun y hy => _
    congr 1
    have y_le_one : 1 ≤ y := by exact (mem_Ico.1 hy).1
    have hy_cancel : (-1 : ℝ) ^ y = (-1 : ℝ) ^ (y - 1 + 1) := by
      rw[Nat.sub_add_cancel y_le_one]
    rw[hy_cancel]
    rw[_root_.pow_succ]
