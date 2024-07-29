import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999

open Function

variable [Group G] {a b c : G}


theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by lean_repl sorry

  by rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]
