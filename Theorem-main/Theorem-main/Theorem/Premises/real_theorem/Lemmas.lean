/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.group_with_zero.units.lemmas
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.GroupTheory.GroupAction.Units

/-!
# Further lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

-/


variable {α M₀ G₀ M₀' G₀' F F' : Type _}

variable [MonoidWithZero M₀]

section GroupWithZero

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
theorem div_self (h : a ≠ 0) : a / a = 1 :=
  IsUnit.div_self h.isUnit
#align div_self div_self

theorem eq_mul_inv_iff_mul_eq₀ (hc : c ≠ 0) : a = b * c⁻¹ ↔ a * c = b :=
  IsUnit.eq_mul_inv_iff_mul_eq hc.isUnit
#align eq_mul_inv_iff_mul_eq₀ eq_mul_inv_iff_mul_eq₀

theorem eq_inv_mul_iff_mul_eq₀ (hb : b ≠ 0) : a = b⁻¹ * c ↔ b * a = c :=
  IsUnit.eq_inv_mul_iff_mul_eq  hb.isUnit
#align eq_inv_mul_iff_mul_eq₀ eq_inv_mul_iff_mul_eq₀

theorem inv_mul_eq_iff_eq_mul₀ (ha : a ≠ 0) : a⁻¹ * b = c ↔ b = a * c :=
  IsUnit.inv_mul_eq_iff_eq_mul ha.isUnit
#align inv_mul_eq_iff_eq_mul₀ inv_mul_eq_iff_eq_mul₀

theorem mul_inv_eq_iff_eq_mul₀ (hb : b ≠ 0) : a * b⁻¹ = c ↔ a = c * b :=
  IsUnit.mul_inv_eq_iff_eq_mul hb.isUnit
#align mul_inv_eq_iff_eq_mul₀ mul_inv_eq_iff_eq_mul₀

theorem mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b :=
  IsUnit.mul_inv_eq_one hb.isUnit
#align mul_inv_eq_one₀ mul_inv_eq_one₀

theorem inv_mul_eq_one₀ (ha : a ≠ 0) : a⁻¹ * b = 1 ↔ a = b :=
  IsUnit.inv_mul_eq_one ha.isUnit
#align inv_mul_eq_one₀ inv_mul_eq_one₀

theorem mul_eq_one_iff_eq_inv₀ (hb : b ≠ 0) : a * b = 1 ↔ a = b⁻¹ :=
  IsUnit.mul_eq_one_iff_eq_inv hb.isUnit
#align mul_eq_one_iff_eq_inv₀ mul_eq_one_iff_eq_inv₀

theorem mul_eq_one_iff_inv_eq₀ (ha : a ≠ 0) : a * b = 1 ↔ a⁻¹ = b :=
  IsUnit.mul_eq_one_iff_inv_eq ha.isUnit
#align mul_eq_one_iff_inv_eq₀ mul_eq_one_iff_inv_eq₀

@[simp]
theorem div_mul_cancel (a : G₀) (h : b ≠ 0) : a / b * b = a :=
  IsUnit.div_mul_cancel h.isUnit _
#align div_mul_cancel div_mul_cancel

@[simp]
theorem mul_div_cancel (a : G₀) (h : b ≠ 0) : a * b / b = a :=
  IsUnit.mul_div_cancel h.isUnit _
#align mul_div_cancel mul_div_cancel

theorem mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 :=
  IsUnit.mul_one_div_cancel h.isUnit
#align mul_one_div_cancel mul_one_div_cancel

theorem one_div_mul_cancel (h : a ≠ 0) : 1 / a * a = 1 :=
  IsUnit.one_div_mul_cancel h.isUnit
#align one_div_mul_cancel one_div_mul_cancel

theorem div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b :=
  IsUnit.div_left_inj hc.isUnit
#align div_left_inj' div_left_inj'

@[field_simps]
theorem div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
  IsUnit.div_eq_iff hb.isUnit
#align div_eq_iff div_eq_iff

@[field_simps]
theorem eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a :=
  IsUnit.eq_div_iff hb.isUnit
#align eq_div_iff eq_div_iff

theorem div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
  (IsUnit.div_eq_iff hb.isUnit).trans eq_comm
#align div_eq_iff_mul_eq div_eq_iff_mul_eq

theorem eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b :=
  IsUnit.eq_div_iff hc.isUnit
#align eq_div_iff_mul_eq eq_div_iff_mul_eq

theorem div_eq_of_eq_mul (hb : b ≠ 0) : a = c * b → a / b = c :=
  IsUnit.div_eq_of_eq_mul hb.isUnit
#align div_eq_of_eq_mul div_eq_of_eq_mul

theorem eq_div_of_mul_eq (hc : c ≠ 0) : a * c = b → a = b / c :=
  IsUnit.eq_div_of_mul_eq hc.isUnit
#align eq_div_of_mul_eq eq_div_of_mul_eq

theorem div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b :=
  IsUnit.div_eq_one_iff_eq hb.isUnit
#align div_eq_one_iff_eq div_eq_one_iff_eq

theorem div_mul_left (hb : b ≠ 0) : b / (a * b) = 1 / a :=
  IsUnit.div_mul_left hb.isUnit
#align div_mul_left div_mul_left

theorem mul_div_mul_right (a b : G₀) (hc : c ≠ 0) : a * c / (b * c) = a / b :=
  IsUnit.mul_div_mul_right hc.isUnit _ _
#align mul_div_mul_right mul_div_mul_right

theorem mul_mul_div (a : G₀) (hb : b ≠ 0) : a = a * b * (1 / b) :=
  (IsUnit.mul_mul_div _ hb.isUnit).symm
#align mul_mul_div mul_mul_div

theorem div_div_div_cancel_right (a : G₀) (hc : c ≠ 0) : a / c / (b / c) = a / b := by
  rw [div_div_eq_mul_div, div_mul_cancel _ hc]
#align div_div_div_cancel_right div_div_div_cancel_right

theorem div_mul_div_cancel (a : G₀) (hc : c ≠ 0) : a / c * (c / b) = a / b := by
  rw [← mul_div_assoc, div_mul_cancel _ hc]
#align div_mul_div_cancel div_mul_div_cancel

theorem div_mul_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a / b * b = a :=
  Classical.by_cases (fun hb : b = 0 => by simp [*]) (div_mul_cancel a)
#align div_mul_cancel_of_imp div_mul_cancel_of_imp

theorem mul_div_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a * b / b = a :=
  Classical.by_cases (fun hb : b = 0 => by simp [*]) (mul_div_cancel a)
#align mul_div_cancel_of_imp mul_div_cancel_of_imp


end GroupWithZero

section CommGroupWithZero

-- comm
variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem div_mul_right (b : G₀) (ha : a ≠ 0) : a / (a * b) = 1 / b :=
  IsUnit.div_mul_right ha.isUnit _
#align div_mul_right div_mul_right

theorem mul_div_cancel_left_of_imp {a b : G₀} (h : a = 0 → b = 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_of_imp h]
#align mul_div_cancel_left_of_imp mul_div_cancel_left_of_imp

theorem mul_div_cancel_left (b : G₀) (ha : a ≠ 0) : a * b / a = b :=
  IsUnit.mul_div_cancel_left ha.isUnit _
#align mul_div_cancel_left mul_div_cancel_left

theorem mul_div_cancel_of_imp' {a b : G₀} (h : b = 0 → a = 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel_of_imp h]
#align mul_div_cancel_of_imp' mul_div_cancel_of_imp'

theorem mul_div_cancel' (a : G₀) (hb : b ≠ 0) : b * (a / b) = a :=
  IsUnit.mul_div_cancel' hb.isUnit _
#align mul_div_cancel' mul_div_cancel'

theorem mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b :=
  IsUnit.mul_div_mul_left hc.isUnit _ _
#align mul_div_mul_left mul_div_mul_left

theorem mul_eq_mul_of_div_eq_div (a : G₀) {b : G₀} (c : G₀) {d : G₀} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a, ← div_self hb, ← mul_comm_div, h, div_mul_eq_mul_div, div_mul_cancel _ hd]
#align mul_eq_mul_of_div_eq_div mul_eq_mul_of_div_eq_div

@[field_simps]
theorem div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
  IsUnit.div_eq_div_iff hb.isUnit hd.isUnit
#align div_eq_div_iff div_eq_div_iff

theorem div_div_cancel' (ha : a ≠ 0) : a / (a / b) = b :=
  IsUnit.div_div_cancel ha.isUnit
#align div_div_cancel' div_div_cancel'

theorem div_div_cancel_left' (ha : a ≠ 0) : a / b / a = b⁻¹ :=
  ha.isUnit.div_div_cancel_left
#align div_div_cancel_left' div_div_cancel_left'

theorem div_helper (b : G₀) (h : a ≠ 0) : 1 / (a * b) * a = 1 / b := by
  rw [div_mul_eq_mul_div, one_mul, div_mul_right _ h]
#align div_helper div_helper

end CommGroupWithZero
