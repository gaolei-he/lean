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

theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]



theorem mul_one_div (x y : G) : x * (1 / y) = x / y :=
  by rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]

theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) :=
  by rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]

theorem div_mul_cancel' (a b : G) : a / b * b = a :=
  by rw [div_eq_mul_inv, inv_mul_cancel_right a b]


theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h ↦ by rw [h, mul_left_inv]⟩

theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]

theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]


-- /////////


theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_right_inv a]


theorem mul_div_cancel'' (a b : G) : a * b / b = a :=
  by rw [div_eq_mul_inv, mul_inv_cancel_right a b]


theorem div_mul_cancel''' (a b : G) : a / (b * a) = b⁻¹ := by rw [← inv_div, mul_div_cancel'']

theorem div_left_inj : b / a = c / a ↔ b = c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_left_inj _



theorem div_mul_div_cancel' (a b c : G) : a / b * (b / c) = a / c :=
  by rw [← mul_div_assoc, div_mul_cancel']


  theorem div_div_div_cancel_right' (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b, div_inv_eq_mul, div_mul_div_cancel']
