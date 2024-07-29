/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module algebra.field.basic
! leanprover-community/mathlib commit 05101c3df9d9cfe9430edc205860c79b6d660102
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
-- import Mathlib.Algebra.Hom.Ring
import Mathlib.Algebra.Ring.Commute

/-!
# Lemmas about division (semi)rings and (semi)fields

-/


open Function OrderDual Set

universe u

variable {α β K : Type _}

section DivisionSemiring

variable [DivisionSemiring α] {a b c d : α}

theorem add_div (a b c : α) : (a + b) / c = a / c + b / c := by simp_rw [div_eq_mul_inv, add_mul]
#align add_div add_div

@[field_simps]
theorem div_add_div_same (a b c : α) : a / c + b / c = (a + b) / c :=
  (add_div _ _ _).symm
#align div_add_div_same div_add_div_same

theorem same_add_div (h : b ≠ 0) : (b + a) / b = 1 + a / b := by rw [← div_self h, add_div]
#align same_add_div same_add_div

theorem div_add_same (h : b ≠ 0) : (a + b) / b = a / b + 1 := by rw [← div_self h, add_div]
#align div_add_same div_add_same

theorem one_add_div (h : b ≠ 0) : 1 + a / b = (b + a) / b :=
  (same_add_div h).symm
#align one_add_div one_add_div

theorem div_add_one (h : b ≠ 0) : a / b + 1 = (a + b) / b :=
  (div_add_same h).symm
#align div_add_one div_add_one

theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (a + b) * (1 / b) = 1 / a + 1 / b := by
  rw [mul_add, one_div_mul_cancel ha, add_mul, one_mul, mul_assoc, mul_one_div_cancel hb, mul_one,
    add_comm]
#align one_div_mul_add_mul_one_div_eq_one_div_add_one_div one_div_mul_add_mul_one_div_eq_one_div_add_one_div

theorem add_div_eq_mul_add_div (a b : α) (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
  (eq_div_iff_mul_eq hc).2 <| by rw [right_distrib, div_mul_cancel _ hc]
#align add_div_eq_mul_add_div add_div_eq_mul_add_div

@[field_simps]
theorem add_div' (a b c : α) (hc : c ≠ 0) : b + a / c = (b * c + a) / c := by
  rw [add_div, mul_div_cancel _ hc]
#align add_div' add_div'

@[field_simps]
theorem div_add' (a b c : α) (hc : c ≠ 0) : a / c + b = (a + b * c) / c := by
  rwa [add_comm, add_div', add_comm]
#align div_add' div_add'


end DivisionSemiring

section DivisionMonoid

variable [DivisionMonoid K] [HasDistribNeg K] {a b : K}

theorem one_div_neg_one_eq_neg_one : (1 : K) / -1 = -1 :=
  have : -1 * -1 = (1 : K) := by rw [neg_mul_neg, one_mul]
  Eq.symm (eq_one_div_of_mul_eq_one_right this)
#align one_div_neg_one_eq_neg_one one_div_neg_one_eq_neg_one

theorem one_div_neg_eq_neg_one_div (a : K) : 1 / -a = -(1 / a) :=
  calc
    1 / -a = 1 / (-1 * a) := by rw [neg_eq_neg_one_mul]
    _ = 1 / a * (1 / -1) := by rw [one_div_mul_one_div_rev]
    _ = 1 / a * -1 := by rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by rw [mul_neg, mul_one]
#align one_div_neg_eq_neg_one_div one_div_neg_eq_neg_one_div

theorem div_neg_eq_neg_div (a b : K) : b / -a = -(b / a) :=
  calc
    b / -a = b * (1 / -a) := by rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by rw [mul_one_div]
#align div_neg_eq_neg_div div_neg_eq_neg_div

theorem neg_div (a b : K) : -b / a = -(b / a) := by
  rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]
#align neg_div neg_div

@[field_simps]
theorem neg_div' (a b : K) : -(b / a) = -b / a := by simp [neg_div]
#align neg_div' neg_div'

theorem neg_div_neg_eq (a b : K) : -a / -b = a / b := by rw [div_neg_eq_neg_div, neg_div, neg_neg]
#align neg_div_neg_eq neg_div_neg_eq

theorem neg_inv : -a⁻¹ = (-a)⁻¹ := by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]
#align neg_inv neg_inv

theorem div_neg (a : K) : a / -b = -(a / b) := by rw [← div_neg_eq_neg_div]
#align div_neg div_neg

theorem inv_neg : (-a)⁻¹ = -a⁻¹ := by rw [neg_inv]
#align inv_neg inv_neg

theorem inv_neg_one : (-1 : K)⁻¹ = -1 := by rw [← neg_inv, inv_one]

end DivisionMonoid

section DivisionRing

variable [DivisionRing K] {a b c d : K}

@[simp]
theorem div_neg_self {a : K} (h : a ≠ 0) : a / -a = -1 := by rw [div_neg_eq_neg_div, div_self h]
#align div_neg_self div_neg_self

@[simp]
theorem neg_div_self {a : K} (h : a ≠ 0) : -a / a = -1 := by rw [neg_div, div_self h]
#align neg_div_self neg_div_self

theorem div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c := by
  rw [sub_eq_add_neg, ← neg_div, div_add_div_same, sub_eq_add_neg]
#align div_sub_div_same div_sub_div_same

theorem same_sub_div {a b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm
#align same_sub_div same_sub_div

theorem one_sub_div {a b : K} (h : b ≠ 0) : 1 - a / b = (b - a) / b :=
  (same_sub_div h).symm
#align one_sub_div one_sub_div

theorem div_sub_same {a b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm
#align div_sub_same div_sub_same

theorem div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b :=
  (div_sub_same h).symm
#align div_sub_one div_sub_one

theorem sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
  (div_sub_div_same _ _ _).symm
#align sub_div sub_div

/-- See `inv_sub_inv` for the more convenient version when `K` is commutative. -/
theorem inv_sub_inv' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹ := by
  rw [mul_sub, sub_mul, mul_inv_cancel_right₀ hb, inv_mul_cancel ha, one_mul]
#align inv_sub_inv' inv_sub_inv'

theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (b - a) * (1 / b) = 1 / a - 1 / b := by
  rw [mul_sub_left_distrib (1 / a), one_div_mul_cancel ha, mul_sub_right_distrib, one_mul,
    mul_assoc, mul_one_div_cancel hb, mul_one]
#align one_div_mul_sub_mul_one_div_eq_one_div_add_one_div one_div_mul_sub_mul_one_div_eq_one_div_add_one_div

end DivisionRing
