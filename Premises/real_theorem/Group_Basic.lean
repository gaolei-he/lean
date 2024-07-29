/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro

! This file was ported from Lean 3 source module algebra.group.basic
! leanprover-community/mathlib commit a07d750983b94c530ab69a726862c2ab6802b38c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Group.Defs

/-!
# Basic lemmas about semigroups, monoids, and groups

This file lists various basic lemmas about semigroups, monoids, and groups. Most proofs are
one-liners from the corresponding axioms. For the definitions of semigroups, monoids and groups, see
`Algebra/Group/Defs.lean`.
-/


open Function

universe u

variable {α β G : Type _}


section CommSemigroup

variable [CommSemigroup G]

@[to_additive]
theorem mul_left_comm : ∀ a b c : G, a * (b * c) = b * (a * c) :=
  left_comm Mul.mul mul_comm mul_assoc
#align mul_left_comm mul_left_comm
#align add_left_comm add_left_comm

@[to_additive]
theorem mul_right_comm : ∀ a b c : G, a * b * c = a * c * b :=
  right_comm Mul.mul mul_comm mul_assoc
#align mul_right_comm mul_right_comm
#align add_right_comm add_right_comm

@[to_additive]
theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) :=
  by simp only [mul_left_comm, mul_assoc]
#align mul_mul_mul_comm mul_mul_mul_comm
#align add_add_add_comm add_add_add_comm

@[to_additive]
theorem mul_rotate (a b c : G) : a * b * c = b * c * a :=
  by simp only [mul_left_comm, mul_comm]
#align mul_rotate mul_rotate
#align add_rotate add_rotate

@[to_additive]
theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) :=
  by simp only [mul_left_comm, mul_comm]
#align mul_rotate' mul_rotate'
#align add_rotate' add_rotate'

end CommSemigroup



section LeftCancelMonoid

variable {M : Type u} [LeftCancelMonoid M] {a b : M}

@[to_additive (attr := simp)]
theorem mul_right_eq_self : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
  _ ↔ b = 1 := mul_left_cancel_iff
#align mul_right_eq_self mul_right_eq_self
#align add_right_eq_self add_right_eq_self

@[to_additive (attr := simp)]
theorem self_eq_mul_right : a = a * b ↔ b = 1 :=
  eq_comm.trans mul_right_eq_self
#align self_eq_mul_right self_eq_mul_right
#align self_eq_add_right self_eq_add_right

@[to_additive]
theorem mul_right_ne_self : a * b ≠ a ↔ b ≠ 1 := mul_right_eq_self.not
#align mul_right_ne_self mul_right_ne_self
#align add_right_ne_self add_right_ne_self

@[to_additive]
theorem self_ne_mul_right : a ≠ a * b ↔ b ≠ 1 := self_eq_mul_right.not
#align self_ne_mul_right self_ne_mul_right
#align self_ne_add_right self_ne_add_right

end LeftCancelMonoid

section RightCancelMonoid

variable {M : Type u} [RightCancelMonoid M] {a b : M}

@[to_additive (attr := simp)]
theorem mul_left_eq_self : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
  _ ↔ a = 1 := mul_right_cancel_iff
#align mul_left_eq_self mul_left_eq_self
#align add_left_eq_self add_left_eq_self

@[to_additive (attr := simp)]
theorem self_eq_mul_left : b = a * b ↔ a = 1 :=
  eq_comm.trans mul_left_eq_self
#align self_eq_mul_left self_eq_mul_left
#align self_eq_add_left self_eq_add_left

@[to_additive]
theorem mul_left_ne_self : a * b ≠ b ↔ a ≠ 1 := mul_left_eq_self.not
#align mul_left_ne_self mul_left_ne_self
#align add_left_ne_self add_left_ne_self

@[to_additive]
theorem self_ne_mul_left : b ≠ a * b ↔ a ≠ 1 := self_eq_mul_left.not
#align self_ne_mul_left self_ne_mul_left
#align self_ne_add_left self_ne_add_left

end RightCancelMonoid



section DivInvMonoid

variable [DivInvMonoid G] {a b c : G}

@[to_additive, field_simps] -- The attributes are out of order on purpose
theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]
#align inv_eq_one_div inv_eq_one_div
#align neg_eq_zero_sub neg_eq_zero_sub

@[to_additive]
theorem mul_one_div (x y : G) : x * (1 / y) = x / y :=
  by rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]
#align mul_one_div mul_one_div
#align add_zero_sub add_zero_sub

@[to_additive]
theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) :=
  by rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]
#align mul_div_assoc mul_div_assoc
#align add_sub_assoc add_sub_assoc

@[to_additive, field_simps] -- The attributes are out of order on purpose
theorem mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c :=
  (mul_div_assoc _ _ _).symm
#align mul_div_assoc' mul_div_assoc'
#align add_sub_assoc' add_sub_assoc'

@[to_additive (attr := simp)]
theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm
#align one_div one_div
#align zero_sub zero_sub

@[to_additive]
theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]
#align mul_div mul_div
#align add_sub add_sub

@[to_additive]
theorem div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) := by rw [div_eq_mul_inv, one_div]
#align div_eq_mul_one_div div_eq_mul_one_div
#align sub_eq_add_zero_sub sub_eq_add_zero_sub

end DivInvMonoid

section DivInvOneMonoid

variable [DivInvOneMonoid G]

@[to_additive (attr := simp)]
theorem div_one (a : G) : a / 1 = a := by simp [div_eq_mul_inv]
#align div_one div_one
#align sub_zero sub_zero

@[to_additive]
theorem one_div_one : (1 : G) / 1 = 1 :=
  div_one _
#align one_div_one one_div_one
#align zero_sub_zero zero_sub_zero

end DivInvOneMonoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv

/-
  这两个定理新版本在：Mathlib/Algebra/Group/Defs.lean
-/

-- @[to_additive]
-- theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a :=
--   by rw [← inv_eq_of_mul_eq_one_right h, inv_inv]
-- #align inv_eq_of_mul_eq_one_left inv_eq_of_mul_eq_one_left
-- #align neg_eq_of_add_eq_zero_left neg_eq_of_add_eq_zero_left

-- @[to_additive]
-- theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
--   (inv_eq_of_mul_eq_one_left h).symm
-- #align eq_inv_of_mul_eq_one_left eq_inv_of_mul_eq_one_left
-- #align eq_neg_of_add_eq_zero_left eq_neg_of_add_eq_zero_left

@[to_additive]
theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right h).symm
#align eq_inv_of_mul_eq_one_right eq_inv_of_mul_eq_one_right
#align eq_neg_of_add_eq_zero_right eq_neg_of_add_eq_zero_right

@[to_additive]
theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a :=
  by rw [eq_inv_of_mul_eq_one_left h, one_div]
#align eq_one_div_of_mul_eq_one_left eq_one_div_of_mul_eq_one_left
#align eq_zero_sub_of_add_eq_zero_left eq_zero_sub_of_add_eq_zero_left

@[to_additive]
theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a :=
  by rw [eq_inv_of_mul_eq_one_right h, one_div]
#align eq_one_div_of_mul_eq_one_right eq_one_div_of_mul_eq_one_right
#align eq_zero_sub_of_add_eq_zero_right eq_zero_sub_of_add_eq_zero_right




variable (a b c)

@[to_additive]
theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp
#align one_div_mul_one_div_rev one_div_mul_one_div_rev
#align zero_sub_add_zero_sub_rev zero_sub_add_zero_sub_rev

@[to_additive]
theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp
#align inv_div_left inv_div_left
#align neg_sub_left neg_sub_left

@[to_additive (attr := simp)]
theorem inv_div : (a / b)⁻¹ = b / a := by simp
#align inv_div inv_div
#align neg_sub neg_sub

@[to_additive]
theorem one_div_div : 1 / (a / b) = b / a := by simp
#align one_div_div one_div_div
#align zero_sub_sub zero_sub_sub

@[to_additive]
theorem one_div_one_div : 1 / (1 / a) = a := by simp
#align one_div_one_div one_div_one_div
#align zero_sub_zero_sub zero_sub_zero_sub


variable {a b c}

@[to_additive]
theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b :=
  by rw [← one_div_one_div a, h, one_div_one_div]
#align eq_of_one_div_eq_one_div eq_of_one_div_eq_one_div
#align eq_of_zero_sub_eq_zero_sub eq_of_zero_sub_eq_zero_sub

variable (a b c)

@[to_additive, field_simps] -- The attributes are out of order on purpose
theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp
#align div_div_eq_mul_div div_div_eq_mul_div
#align sub_sub_eq_add_sub sub_sub_eq_add_sub

@[to_additive (attr := simp)]
theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp
#align div_inv_eq_mul div_inv_eq_mul
#align sub_neg_eq_add sub_neg_eq_add

@[to_additive]
theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b :=
  by simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]
#align div_mul_eq_div_div_swap div_mul_eq_div_div_swap
#align sub_add_eq_sub_sub_swap sub_add_eq_sub_sub_swap

end DivisionMonoid


section DivisionCommMonoid

variable [DivisionCommMonoid α] (a b c d : α)

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive neg_add]
theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp
#align mul_inv mul_inv
#align neg_add neg_add

@[to_additive]
theorem inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹ := by simp
#align inv_div' inv_div'
#align neg_sub' neg_sub'

@[to_additive]
theorem div_eq_inv_mul : a / b = b⁻¹ * a := by simp
#align div_eq_inv_mul div_eq_inv_mul
#align sub_eq_neg_add sub_eq_neg_add

@[to_additive]
theorem inv_mul_eq_div : a⁻¹ * b = b / a := by simp
#align inv_mul_eq_div inv_mul_eq_div
#align neg_add_eq_sub neg_add_eq_sub

@[to_additive]
theorem inv_mul' : (a * b)⁻¹ = a⁻¹ / b := by simp
#align inv_mul' inv_mul'
#align neg_add' neg_add'

@[to_additive]
theorem inv_div_inv : a⁻¹ / b⁻¹ = b / a := by simp
#align inv_div_inv inv_div_inv
#align neg_sub_neg neg_sub_neg

@[to_additive]
theorem inv_inv_div_inv : (a⁻¹ / b⁻¹)⁻¹ = a / b := by simp
#align inv_inv_div_inv inv_inv_div_inv
#align neg_neg_sub_neg neg_neg_sub_neg

@[to_additive]
theorem one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b) := by simp
#align one_div_mul_one_div one_div_mul_one_div
#align zero_sub_add_zero_sub zero_sub_add_zero_sub

@[to_additive]
theorem div_right_comm : a / b / c = a / c / b := by simp
#align div_right_comm div_right_comm
#align sub_right_comm sub_right_comm

@[to_additive, field_simps]
theorem div_div : a / b / c = a / (b * c) := by simp
#align div_div div_div
#align sub_sub sub_sub

@[to_additive]
theorem div_mul : a / b * c = a / (b / c) := by simp
#align div_mul div_mul
#align sub_add sub_add

@[to_additive]
theorem mul_div_left_comm : a * (b / c) = b * (a / c) := by simp
#align mul_div_left_comm mul_div_left_comm
#align add_sub_left_comm add_sub_left_comm

@[to_additive]
theorem mul_div_right_comm : a * b / c = a / c * b := by simp
#align mul_div_right_comm mul_div_right_comm
#align add_sub_right_comm add_sub_right_comm

@[to_additive]
theorem div_mul_eq_div_div : a / (b * c) = a / b / c := by simp
#align div_mul_eq_div_div div_mul_eq_div_div
#align sub_add_eq_sub_sub sub_add_eq_sub_sub

@[to_additive, field_simps]
theorem div_mul_eq_mul_div : a / b * c = a * c / b := by simp
#align div_mul_eq_mul_div div_mul_eq_mul_div
#align sub_add_eq_add_sub sub_add_eq_add_sub

@[to_additive]
theorem mul_comm_div : a / b * c = a * (c / b) := by simp
#align mul_comm_div mul_comm_div
#align add_comm_sub add_comm_sub

@[to_additive]
theorem div_mul_comm : a / b * c = c / b * a := by simp
#align div_mul_comm div_mul_comm
#align sub_add_comm sub_add_comm

@[to_additive]
theorem div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c) := by simp
#align div_mul_eq_div_mul_one_div div_mul_eq_div_mul_one_div
#align sub_add_eq_sub_add_zero_sub sub_add_eq_sub_add_zero_sub

@[to_additive]
theorem div_div_div_eq : a / b / (c / d) = a * d / (b * c) := by simp
#align div_div_div_eq div_div_div_eq
#align sub_sub_sub_eq sub_sub_sub_eq

@[to_additive]
theorem div_div_div_comm : a / b / (c / d) = a / c / (b / d) := by simp
#align div_div_div_comm div_div_div_comm
#align sub_sub_sub_comm sub_sub_sub_comm

@[to_additive]
theorem div_mul_div_comm : a / b * (c / d) = a * c / (b * d) := by simp
#align div_mul_div_comm div_mul_div_comm
#align sub_add_sub_comm sub_add_sub_comm

@[to_additive]
theorem mul_div_mul_comm : a * b / (c * d) = a / c * (b / d) := by simp
#align mul_div_mul_comm mul_div_mul_comm
#align add_sub_add_comm add_sub_add_comm

end DivisionCommMonoid

section Group

variable [Group G] {a b c d : G}

@[to_additive (attr := simp)]
theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by rw [div_eq_mul_inv, mul_left_eq_self]
#align div_eq_inv_self div_eq_inv_self
#align sub_eq_neg_self sub_eq_neg_self


@[to_additive]
theorem eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ := by simp [h.symm]
#align eq_mul_inv_of_mul_eq eq_mul_inv_of_mul_eq
#align eq_add_neg_of_add_eq eq_add_neg_of_add_eq

@[to_additive]
theorem eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c := by simp [h.symm]
#align eq_inv_mul_of_mul_eq eq_inv_mul_of_mul_eq
#align eq_neg_add_of_add_eq eq_neg_add_of_add_eq

@[to_additive]
theorem inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c := by simp [h]
#align inv_mul_eq_of_eq_mul inv_mul_eq_of_eq_mul
#align neg_add_eq_of_eq_add neg_add_eq_of_eq_add

@[to_additive]
theorem mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c := by simp [h]
#align mul_inv_eq_of_eq_mul mul_inv_eq_of_eq_mul
#align add_neg_eq_of_eq_add add_neg_eq_of_eq_add

@[to_additive]
theorem eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c := by simp [h.symm]
#align eq_mul_of_mul_inv_eq eq_mul_of_mul_inv_eq
#align eq_add_of_add_neg_eq eq_add_of_add_neg_eq

@[to_additive]
theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c := by simp [h.symm, mul_inv_cancel_left]
#align eq_mul_of_inv_mul_eq eq_mul_of_inv_mul_eq
#align eq_add_of_neg_add_eq eq_add_of_neg_add_eq

@[to_additive]
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by rw [h, mul_inv_cancel_left]
#align mul_eq_of_eq_inv_mul mul_eq_of_eq_inv_mul
#align add_eq_of_eq_neg_add add_eq_of_eq_neg_add

@[to_additive]
theorem mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c := by simp [h]
#align mul_eq_of_eq_mul_inv mul_eq_of_eq_mul_inv
#align add_eq_of_eq_add_neg add_eq_of_eq_add_neg

@[to_additive]
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h ↦ by rw [h, mul_left_inv]⟩
#align mul_eq_one_iff_eq_inv mul_eq_one_iff_eq_inv
#align add_eq_zero_iff_eq_neg add_eq_zero_iff_eq_neg



@[to_additive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm
#align eq_inv_iff_mul_eq_one eq_inv_iff_mul_eq_one
#align eq_neg_iff_add_eq_zero eq_neg_iff_add_eq_zero


@[to_additive]
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨fun h ↦ by rw [h, inv_mul_cancel_right], fun h ↦ by rw [← h, mul_inv_cancel_right]⟩
#align eq_mul_inv_iff_mul_eq eq_mul_inv_iff_mul_eq
#align eq_add_neg_iff_add_eq eq_add_neg_iff_add_eq

@[to_additive]
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨fun h ↦ by rw [h, mul_inv_cancel_left], fun h ↦ by rw [← h, inv_mul_cancel_left]⟩
#align eq_inv_mul_iff_mul_eq eq_inv_mul_iff_mul_eq
#align eq_neg_add_iff_add_eq eq_neg_add_iff_add_eq

@[to_additive]
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h ↦ by rw [← h, mul_inv_cancel_left], fun h ↦ by rw [h, inv_mul_cancel_left]⟩
#align inv_mul_eq_iff_eq_mul inv_mul_eq_iff_eq_mul
#align neg_add_eq_iff_eq_add neg_add_eq_iff_eq_add

@[to_additive]
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨fun h ↦ by rw [← h, inv_mul_cancel_right], fun h ↦ by rw [h, mul_inv_cancel_right]⟩
#align mul_inv_eq_iff_eq_mul mul_inv_eq_iff_eq_mul
#align add_neg_eq_iff_eq_add add_neg_eq_iff_eq_add

@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]
#align mul_inv_eq_one mul_inv_eq_one
#align add_neg_eq_zero add_neg_eq_zero




@[to_additive (attr := simp) sub_add_cancel]
theorem div_mul_cancel' (a b : G) : a / b * b = a :=
  by rw [div_eq_mul_inv, inv_mul_cancel_right a b]
#align div_mul_cancel' div_mul_cancel'
#align sub_add_cancel sub_add_cancel

@[to_additive (attr := simp) sub_self]
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_right_inv a]
#align div_self' div_self'
#align sub_self sub_self

@[to_additive (attr := simp) add_sub_cancel]
theorem mul_div_cancel'' (a b : G) : a * b / b = a :=
  by rw [div_eq_mul_inv, mul_inv_cancel_right a b]
#align mul_div_cancel'' mul_div_cancel''
#align add_sub_cancel add_sub_cancel

@[to_additive (attr := simp) sub_add_cancel'']
theorem div_mul_cancel''' (a b : G) : a / (b * a) = b⁻¹ := by rw [← inv_div, mul_div_cancel'']
#align div_mul_cancel''' div_mul_cancel'''
#align sub_add_cancel'' sub_add_cancel''

@[to_additive (attr := simp)]
theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  rw [div_mul_eq_div_div_swap]; simp only [mul_left_inj, eq_self_iff_true, mul_div_cancel'']
#align mul_div_mul_right_eq_div mul_div_mul_right_eq_div
#align add_sub_add_right_eq_sub add_sub_add_right_eq_sub

@[to_additive eq_sub_of_add_eq]
theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]
#align eq_div_of_mul_eq' eq_div_of_mul_eq'
#align eq_sub_of_add_eq eq_sub_of_add_eq

@[to_additive sub_eq_of_eq_add]
theorem div_eq_of_eq_mul'' (h : a = c * b) : a / b = c := by simp [h]
#align div_eq_of_eq_mul'' div_eq_of_eq_mul''
#align sub_eq_of_eq_add sub_eq_of_eq_add

@[to_additive]
theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]
#align eq_mul_of_div_eq eq_mul_of_div_eq
#align eq_add_of_sub_eq eq_add_of_sub_eq

@[to_additive]
theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by simp [h]
#align mul_eq_of_eq_div mul_eq_of_eq_div
#align add_eq_of_eq_sub add_eq_of_eq_sub



@[to_additive (attr := simp)]
theorem div_left_inj : b / a = c / a ↔ b = c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_left_inj _
#align div_left_inj div_left_inj
#align sub_left_inj sub_left_inj

@[to_additive (attr := simp) sub_add_sub_cancel]
theorem div_mul_div_cancel' (a b c : G) : a / b * (b / c) = a / c :=
  by rw [← mul_div_assoc, div_mul_cancel']
#align div_mul_div_cancel' div_mul_div_cancel'
#align sub_add_sub_cancel sub_add_sub_cancel

@[to_additive (attr := simp) sub_sub_sub_cancel_right]
theorem div_div_div_cancel_right' (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b, div_inv_eq_mul, div_mul_div_cancel']
#align div_div_div_cancel_right' div_div_div_cancel_right'
#align sub_sub_sub_cancel_right sub_sub_sub_cancel_right




@[to_additive eq_sub_iff_add_eq]
theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]
#align eq_div_iff_mul_eq' eq_div_iff_mul_eq'
#align eq_sub_iff_add_eq eq_sub_iff_add_eq

@[to_additive]
theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]
#align div_eq_iff_eq_mul div_eq_iff_eq_mul
#align sub_eq_iff_eq_add sub_eq_iff_eq_add



end Group

section CommGroup

variable [CommGroup G] {a b c d : G}

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive]
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]
#align div_eq_of_eq_mul' div_eq_of_eq_mul'
#align sub_eq_of_eq_add' sub_eq_of_eq_add'

@[to_additive (attr := simp)]
theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by
  rw [div_eq_mul_inv, mul_inv_rev, mul_comm b⁻¹ c⁻¹, mul_comm c a, mul_assoc, ←mul_assoc c,
    mul_right_inv, one_mul, div_eq_mul_inv]
#align mul_div_mul_left_eq_div mul_div_mul_left_eq_div
#align add_sub_add_left_eq_sub add_sub_add_left_eq_sub

@[to_additive eq_sub_of_add_eq']
theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]
#align eq_div_of_mul_eq'' eq_div_of_mul_eq''
#align eq_sub_of_add_eq' eq_sub_of_add_eq'

@[to_additive]
theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]
#align eq_mul_of_div_eq' eq_mul_of_div_eq'
#align eq_add_of_sub_eq' eq_add_of_sub_eq'

@[to_additive]
theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by
  simp [h]
  rw [mul_comm c, mul_inv_cancel_left]
#align mul_eq_of_eq_div' mul_eq_of_eq_div'
#align add_eq_of_eq_sub' add_eq_of_eq_sub'

@[to_additive sub_sub_self]
theorem div_div_self' (a b : G) : a / (a / b) = b := by simpa using mul_inv_cancel_left a b
#align div_div_self' div_div_self'
#align sub_sub_self sub_sub_self

@[to_additive]
theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by simp [mul_left_comm c]
#align div_eq_div_mul_div div_eq_div_mul_div
#align sub_eq_sub_add_sub sub_eq_sub_add_sub

@[to_additive (attr := simp)]
theorem div_div_cancel (a b : G) : a / (a / b) = b :=
  div_div_self' a b
#align div_div_cancel div_div_cancel
#align sub_sub_cancel sub_sub_cancel

@[to_additive (attr := simp)]
theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by simp
#align div_div_cancel_left div_div_cancel_left
#align sub_sub_cancel_left sub_sub_cancel_left

@[to_additive eq_sub_iff_add_eq']
theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]
#align eq_div_iff_mul_eq'' eq_div_iff_mul_eq''
#align eq_sub_iff_add_eq' eq_sub_iff_add_eq'

@[to_additive]
theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]
#align div_eq_iff_eq_mul' div_eq_iff_eq_mul'
#align sub_eq_iff_eq_add' sub_eq_iff_eq_add'

@[to_additive (attr := simp) add_sub_cancel']
theorem mul_div_cancel''' (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]
#align mul_div_cancel''' mul_div_cancel'''
#align add_sub_cancel' add_sub_cancel'

@[to_additive (attr := simp)]
theorem mul_div_cancel'_right (a b : G) : a * (b / a) = b := by
  rw [← mul_div_assoc, mul_div_cancel''']
#align mul_div_cancel'_right mul_div_cancel'_right
#align add_sub_cancel'_right add_sub_cancel'_right

@[to_additive (attr := simp) sub_add_cancel']
theorem div_mul_cancel'' (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel''']
#align div_mul_cancel'' div_mul_cancel''
#align sub_add_cancel' sub_add_cancel'

-- This lemma is in the `simp` set under the name `mul_inv_cancel_comm_assoc`,
-- along with the additive version `add_neg_cancel_comm_assoc`,
-- defined  in `Algebra.Group.Commute`
@[to_additive]
theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b := by
  rw [← div_eq_mul_inv, mul_div_cancel'_right a b]
#align mul_mul_inv_cancel'_right mul_mul_inv_cancel'_right
#align add_add_neg_cancel'_right add_add_neg_cancel'_right

@[to_additive (attr := simp)]
theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by
  rw [mul_assoc, mul_div_cancel'_right]
#align mul_mul_div_cancel mul_mul_div_cancel
#align add_add_sub_cancel add_add_sub_cancel

@[to_additive (attr := simp)]
theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b := by
  rw [mul_left_comm, div_mul_cancel', mul_comm]
#align div_mul_mul_cancel div_mul_mul_cancel
#align sub_add_add_cancel sub_add_add_cancel

@[to_additive (attr := simp) sub_add_sub_cancel']
theorem div_mul_div_cancel'' (a b c : G) : a / b * (c / a) = c / b := by
  rw [mul_comm]; apply div_mul_div_cancel'
#align div_mul_div_cancel'' div_mul_div_cancel''
#align sub_add_sub_cancel' sub_add_sub_cancel'

@[to_additive (attr := simp)]
theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by
  rw [← div_mul, mul_div_cancel''']
#align mul_div_div_cancel mul_div_div_cancel
#align add_sub_sub_cancel add_sub_sub_cancel

@[to_additive (attr := simp)]
theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  rw [← inv_div b c, div_inv_eq_mul, mul_comm, div_mul_div_cancel']
#align div_div_div_cancel_left div_div_div_cancel_left
#align sub_sub_sub_cancel_left sub_sub_sub_cancel_left

@[to_additive]
theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]
#align div_eq_div_iff_mul_eq_mul div_eq_div_iff_mul_eq_mul
#align sub_eq_sub_iff_add_eq_add sub_eq_sub_iff_add_eq_add

@[to_additive]
theorem div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, div_eq_iff_eq_mul', mul_div_assoc]
#align div_eq_div_iff_div_eq_div div_eq_div_iff_div_eq_div
#align sub_eq_sub_iff_sub_eq_sub sub_eq_sub_iff_sub_eq_sub

end CommGroup
