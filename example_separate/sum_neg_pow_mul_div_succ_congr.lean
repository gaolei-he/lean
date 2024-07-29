import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Lean4Repl

open Finset

open BigOperators

set_option maxHeartbeats 999999999999999999999999
theorem sum_neg_pow_mul_div_succ_congr : ∑ x in range (n + 1), (-1 : ℝ) ^ x * (1 / (x + 1)) * (Nat.choose (n + 1) (x + 1)) = ∑ x in range (n + 2 - 1), (-1 : ℝ) ^ ( 1 + x + 1 ) * (1 / (1 + x)) * (Nat.choose (n + 1) (1 + x)) := by lean_repl sorry
  simp
  refine' sum_congr rfl fun y _ => _
  congr 2
  rw[add_comm, ← add_assoc]
  norm_num
  rw[pow_add]
  simp
  rw[add_comm]
  rw[add_comm y 1]
