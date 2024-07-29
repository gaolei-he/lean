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

theorem div_mul_div_cancel' (a b c : G) : a / b * (b / c) = a / c := by lean_repl sorry
  by rw [← mul_div_assoc, div_mul_cancel']
