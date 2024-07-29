import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999


open Function

variable [Group G] {a b c : G}


theorem div_mul_cancel' (a b : G) : a / b * b = a := by lean_repl sorry
  by rw [div_eq_mul_inv, inv_mul_cancel_right a b]
