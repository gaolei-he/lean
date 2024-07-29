import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999


open Function

variable [Group G] {a b c : G}



theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ := by lean_repl sorry
  ⟨eq_inv_of_mul_eq_one_left, fun h ↦ by rw [h, mul_left_inv]⟩
