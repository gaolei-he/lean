import Mathlib.Init.ZeroOne
import Mathlib.Init.Data.Int.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Basic
import Mathlib.Algebra.Group.Defs
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999


variable [Group G] {a b c : G}



theorem inv_mul_cancel_left0 (a b : G) : a⁻¹ * (a * b) = b := by lean_repl sorry

by rw [← mul_assoc, mul_left_inv, one_mul]
