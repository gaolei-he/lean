import Mathlib.Data.Real.Basic


theorem pow_neg_succ_succ{ y : ℕ }: (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + y + 1) := by
  rw[add_comm, ← add_assoc]
  norm_num
  rw[pow_add]
  simp
