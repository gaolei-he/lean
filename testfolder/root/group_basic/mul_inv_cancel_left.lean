import Mathlib.Init.ZeroOne
import Mathlib.Init.Data.Int.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Basic
import Mathlib.Algebra.Group.Defs
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999

/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/

#align_import algebra.group.defs from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

variable [Group G] {a b c : G}



theorem mul_inv_cancel_left0 (a b : G) : a * (a⁻¹ * b) = b := by lean_repl sorry

  by rw [← mul_assoc, mul_right_inv, one_mul]
