/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.group_with_zero.basic
! leanprover-community/mathlib commit e8638a0fcaf73e4500469f368ef9494e495099b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Group.OrderSynonym

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

Various lemmas about `GroupWithZero` and `CommGroupWithZero`.
To reduce import dependencies, the type-classes themselves are in
`Algebra.GroupWithZero.Defs`.

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/


open Classical

open Function

variable {α M₀ G₀ M₀' G₀' F F' : Type _}

section

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

theorem left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 :=
  mt fun h => mul_eq_zero_of_left h b
#align left_ne_zero_of_mul left_ne_zero_of_mul

theorem right_ne_zero_of_mul : a * b ≠ 0 → b ≠ 0 :=
  mt (mul_eq_zero_of_right a)
#align right_ne_zero_of_mul right_ne_zero_of_mul

theorem ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
#align ne_zero_and_ne_zero_of_mul ne_zero_and_ne_zero_of_mul

theorem mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a ≠ 0 → b = 0) : a * b = 0 :=
  if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]
#align mul_eq_zero_of_ne_zero_imp_eq_zero mul_eq_zero_of_ne_zero_imp_eq_zero

-- /-- To match `one_mul_eq_id`. -/
-- theorem zero_mul_eq_const : (· * ·) (0 : M₀) = Function.const _ 0 :=
--   funext zero_mul
-- #align zero_mul_eq_const zero_mul_eq_const

-- /-- To match `mul_one_eq_id`. -/
-- theorem mul_zero_eq_const : (· * (0 : M₀)) = Function.const _ 0 :=
--   funext mul_zero
-- #align mul_zero_eq_const mul_zero_eq_const

end MulZeroClass

section Mul

variable [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}

theorem eq_zero_of_mul_self_eq_zero (h : a * a = 0) : a = 0 :=
  (eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id
#align eq_zero_of_mul_self_eq_zero eq_zero_of_mul_self_eq_zero

@[field_simps]
theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  mt eq_zero_or_eq_zero_of_mul_eq_zero <| not_or.mpr ⟨ha, hb⟩
#align mul_ne_zero mul_ne_zero

end Mul

end

section

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

theorem left_ne_zero_of_mul_eq_one (h : a * b = 1) : a ≠ 0 :=
  left_ne_zero_of_mul <| ne_zero_of_eq_one h
#align left_ne_zero_of_mul_eq_one left_ne_zero_of_mul_eq_one

theorem right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 :=
  right_ne_zero_of_mul <| ne_zero_of_eq_one h
#align right_ne_zero_of_mul_eq_one right_ne_zero_of_mul_eq_one

end

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}


@[simp]
theorem mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 := by
  by_cases hc : c = 0 <;> [simp [hc]; simp [mul_left_inj', hc]]
#align mul_eq_mul_right_iff mul_eq_mul_right_iff

@[simp]
theorem mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 := by
  by_cases ha : a = 0 <;> [simp [ha]; simp [mul_right_inj', ha]]
#align mul_eq_mul_left_iff mul_eq_mul_left_iff

theorem mul_right_eq_self₀ : a * b = a ↔ b = 1 ∨ a = 0 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff
#align mul_right_eq_self₀ mul_right_eq_self₀


theorem mul_left_eq_self₀ : a * b = b ↔ a = 1 ∨ b = 0 :=
  calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff
#align mul_left_eq_self₀ mul_left_eq_self₀

@[simp]
theorem mul_eq_left₀ (ha : a ≠ 0) : a * b = a ↔ b = 1 := by
  rw [Iff.comm, ← mul_right_inj' ha, mul_one]
#align mul_eq_left₀ mul_eq_left₀

@[simp]
theorem mul_eq_right₀ (hb : b ≠ 0) : a * b = b ↔ a = 1 := by
  rw [Iff.comm, ← mul_left_inj' hb, one_mul]
#align mul_eq_right₀ mul_eq_right₀

@[simp]
theorem left_eq_mul₀ (ha : a ≠ 0) : a = a * b ↔ b = 1 := by rw [eq_comm, mul_eq_left₀ ha]
#align left_eq_mul₀ left_eq_mul₀

@[simp]
theorem right_eq_mul₀ (hb : b ≠ 0) : b = a * b ↔ a = 1 := by rw [eq_comm, mul_eq_right₀ hb]
#align right_eq_mul₀ right_eq_mul₀

end CancelMonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c g h x : G₀}

@[simp]
theorem inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b⁻¹ * b = a :=
  calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by simp [h]
#align inv_mul_cancel_right₀ inv_mul_cancel_right₀


@[simp]
theorem inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]
#align inv_mul_cancel_left₀ inv_mul_cancel_left₀

end GroupWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
theorem zero_div (a : G₀) : 0 / a = 0 := by rw [div_eq_mul_inv, zero_mul]
#align zero_div zero_div

@[simp]
theorem div_zero (a : G₀) : a / 0 = 0 := by rw [div_eq_mul_inv, inv_zero, mul_zero]
#align div_zero div_zero

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_assoc, mul_inv_cancel h, mul_one]
#align mul_self_mul_inv mul_self_mul_inv


/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_inv_mul_self (a : G₀) : a * a⁻¹ * a = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_inv_cancel h, one_mul]
#align mul_inv_mul_self mul_inv_mul_self


/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp]
theorem inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [inv_mul_cancel h, one_mul]
#align inv_mul_mul_self inv_mul_mul_self


/-- Multiplying `a` by itself and then dividing by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem mul_self_div_self (a : G₀) : a * a / a = a := by rw [div_eq_mul_inv, mul_self_mul_inv a]
#align mul_self_div_self mul_self_div_self

/-- Dividing `a` by itself and then multiplying by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem div_self_mul_self (a : G₀) : a / a * a = a := by rw [div_eq_mul_inv, mul_inv_mul_self a]
#align div_self_mul_self div_self_mul_self

attribute [local simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

theorem one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 := by
  simpa only [one_div] using inv_ne_zero h
#align one_div_ne_zero one_div_ne_zero

theorem ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 := fun ha : a = 0 => by
  rw [ha, div_zero] at h
  contradiction
#align ne_zero_of_one_div_ne_zero ne_zero_of_one_div_ne_zero

theorem eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
  Classical.byCases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim
#align eq_zero_of_one_div_eq_zero eq_zero_of_one_div_eq_zero


end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem div_mul_eq_mul_div₀ (a b c : G₀) : a / c * b = a * b / c := by
  simp_rw [div_eq_mul_inv, mul_assoc, mul_comm c⁻¹]
#align div_mul_eq_mul_div₀ div_mul_eq_mul_div₀

end CommGroupWithZero
