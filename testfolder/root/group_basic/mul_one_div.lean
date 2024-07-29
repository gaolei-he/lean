import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999


open Function

variable [Group G] {a b c : G}


theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by lean_repl sorry

  by rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]
