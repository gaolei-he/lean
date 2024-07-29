/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Mathlib.Init.ZeroOne
import Mathlib.Init.Data.Int.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Basic
import Mathlib.Algebra.Group.Defs

#align_import algebra.group.defs from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

variable [Group G] {a b c : G}


theorem inv_mul_cancel_left0 (a b : G) : a⁻¹ * (a * b) = b :=
by rw [← mul_assoc, mul_left_inv, one_mul]

theorem mul_inv_cancel_left0 (a b : G) : a * (a⁻¹ * b) = b :=
  by rw [← mul_assoc, mul_right_inv, one_mul]

theorem mul_inv_cancel_right0 (a b : G) : a * b * b⁻¹ = a :=
  by rw [mul_assoc, mul_right_inv, mul_one]

theorem inv_mul_cancel_right0(a b : G) : a * b⁻¹ * b = a :=
  by rw [mul_assoc, mul_left_inv, mul_one]


theorem inv_eq_of_mul_eq_one_left0 (h : a * b = 1) : b⁻¹ = a :=
  by rw [← inv_eq_of_mul_eq_one_right h, inv_inv]
