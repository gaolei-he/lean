import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999

/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/

open Function

variable [Group G] {a b c : G}


theorem div_mul_cancel''' (a b : G) : a / (b * a) = b⁻¹ := by lean_repl sorry
 by rw [← inv_div, mul_div_cancel'']
