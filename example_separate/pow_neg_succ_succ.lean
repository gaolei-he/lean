import Mathlib.Data.Real.Basic
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999

theorem pow_neg_succ_succ{ y : ℕ }: (-1 : ℝ) ^ y = (-1 : ℝ) ^ (1 + y + 1) := by lean_repl sorry
  rw[add_comm, ← add_assoc]
  norm_num
  rw[pow_add]
  simp
