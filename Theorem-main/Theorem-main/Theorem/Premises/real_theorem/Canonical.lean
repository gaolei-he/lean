/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs

#align_import algebra.order.sub.canonical from "leanprover-community/mathlib"@"62a5626868683c104774de8d85b9855234ac807c"

/-!
# Lemmas about subtraction in canonically ordered monoids
-/


variable {α : Type*}

section ExistsAddOfLE

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [Sub α] [OrderedSub α] {a b c d : α}

@[simp]
theorem add_tsub_cancel_of_le (h : a ≤ b) : a + (b - a) = b := by
  refine' le_antisymm _ le_add_tsub
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  exact add_le_add_left add_tsub_le_left a
#align add_tsub_cancel_of_le add_tsub_cancel_of_le

theorem tsub_add_cancel_of_le (h : a ≤ b) : b - a + a = b := by
  rw [add_comm]
  exact add_tsub_cancel_of_le h
#align tsub_add_cancel_of_le tsub_add_cancel_of_le

theorem tsub_add_tsub_cancel (hab : b ≤ a) (hcb : c ≤ b) : a - b + (b - c) = a - c := by
  convert tsub_add_cancel_of_le (tsub_le_tsub_right hab c) using 2
  rw [tsub_tsub, add_tsub_cancel_of_le hcb]
#align tsub_add_tsub_cancel tsub_add_tsub_cancel

theorem tsub_tsub_tsub_cancel_right (h : c ≤ b) : a - c - (b - c) = a - b := by
  rw [tsub_tsub, add_tsub_cancel_of_le h]
#align tsub_tsub_tsub_cancel_right tsub_tsub_tsub_cancel_right

/-! #### Lemmas that assume that an element is `AddLECancellable`. -/


namespace AddLECancellable

protected theorem eq_tsub_iff_add_eq_of_le (hc : AddLECancellable c) (h : c ≤ b) :
    a = b - c ↔ a + c = b :=
  ⟨by
    rintro rfl
    exact tsub_add_cancel_of_le h, hc.eq_tsub_of_add_eq⟩
#align add_le_cancellable.eq_tsub_iff_add_eq_of_le AddLECancellable.eq_tsub_iff_add_eq_of_le

protected theorem tsub_eq_iff_eq_add_of_le (hb : AddLECancellable b) (h : b ≤ a) :
    a - b = c ↔ a = c + b := by rw [eq_comm, hb.eq_tsub_iff_add_eq_of_le h, eq_comm]
#align add_le_cancellable.tsub_eq_iff_eq_add_of_le AddLECancellable.tsub_eq_iff_eq_add_of_le

protected theorem add_tsub_assoc_of_le (hc : AddLECancellable c) (h : c ≤ b) (a : α) :
    a + b - c = a + (b - c) := by
  conv_lhs => rw [← add_tsub_cancel_of_le h, add_comm c, ← add_assoc, hc.add_tsub_cancel_right]
#align add_le_cancellable.add_tsub_assoc_of_le AddLECancellable.add_tsub_assoc_of_le

protected theorem tsub_add_eq_add_tsub (hb : AddLECancellable b) (h : b ≤ a) :
    a - b + c = a + c - b := by rw [add_comm a, hb.add_tsub_assoc_of_le h, add_comm]
#align add_le_cancellable.tsub_add_eq_add_tsub AddLECancellable.tsub_add_eq_add_tsub

protected theorem tsub_tsub_assoc (hbc : AddLECancellable (b - c)) (h₁ : b ≤ a) (h₂ : c ≤ b) :
    a - (b - c) = a - b + c :=
  hbc.tsub_eq_of_eq_add <| by rw [add_assoc, add_tsub_cancel_of_le h₂, tsub_add_cancel_of_le h₁]
#align add_le_cancellable.tsub_tsub_assoc AddLECancellable.tsub_tsub_assoc

protected theorem tsub_add_tsub_comm (hb : AddLECancellable b) (hd : AddLECancellable d)
    (hba : b ≤ a) (hdc : d ≤ c) : a - b + (c - d) = a + c - (b + d) := by
  rw [hb.tsub_add_eq_add_tsub hba, ← hd.add_tsub_assoc_of_le hdc, tsub_tsub, add_comm d]
#align add_le_cancellable.tsub_add_tsub_comm AddLECancellable.tsub_add_tsub_comm

protected theorem tsub_lt_iff_left (hb : AddLECancellable b) (hba : b ≤ a) :
    a - b < c ↔ a < b + c := by
  refine' ⟨hb.lt_add_of_tsub_lt_left, _⟩
  intro h; refine' (tsub_le_iff_left.mpr h.le).lt_of_ne _
  rintro rfl; exact h.ne' (add_tsub_cancel_of_le hba)
#align add_le_cancellable.tsub_lt_iff_left AddLECancellable.tsub_lt_iff_left

protected theorem tsub_lt_iff_right (hb : AddLECancellable b) (hba : b ≤ a) :
    a - b < c ↔ a < c + b := by
  rw [add_comm]
  exact hb.tsub_lt_iff_left hba
#align add_le_cancellable.tsub_lt_iff_right AddLECancellable.tsub_lt_iff_right

protected theorem tsub_lt_iff_tsub_lt (hb : AddLECancellable b) (hc : AddLECancellable c)
    (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b := by
  rw [hb.tsub_lt_iff_left h₁, hc.tsub_lt_iff_right h₂]
#align add_le_cancellable.tsub_lt_iff_tsub_lt AddLECancellable.tsub_lt_iff_tsub_lt

protected theorem tsub_inj_right (hab : AddLECancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a)
    (h₃ : a - b = a - c) : b = c := by
  rw [← hab.inj]
  rw [tsub_add_cancel_of_le h₁, h₃, tsub_add_cancel_of_le h₂]
#align add_le_cancellable.tsub_inj_right AddLECancellable.tsub_inj_right

protected theorem lt_of_tsub_lt_tsub_left_of_le [ContravariantClass α α (· + ·) (· < ·)]
    (hb : AddLECancellable b) (hca : c ≤ a) (h : a - b < a - c) : c < b := by
  conv_lhs at h => rw [← tsub_add_cancel_of_le hca]
  exact lt_of_add_lt_add_left (hb.lt_add_of_tsub_lt_right h)
#align add_le_cancellable.lt_of_tsub_lt_tsub_left_of_le AddLECancellable.lt_of_tsub_lt_tsub_left_of_le

protected theorem tsub_lt_tsub_left_of_le (hab : AddLECancellable (a - b)) (h₁ : b ≤ a)
    (h : c < b) : a - b < a - c :=
  (tsub_le_tsub_left h.le _).lt_of_ne fun h' => h.ne' <| hab.tsub_inj_right h₁ (h.le.trans h₁) h'
#align add_le_cancellable.tsub_lt_tsub_left_of_le AddLECancellable.tsub_lt_tsub_left_of_le

protected theorem tsub_lt_tsub_right_of_le (hc : AddLECancellable c) (h : c ≤ a) (h2 : a < b) :
    a - c < b - c := by
  apply hc.lt_tsub_of_add_lt_left
  rwa [add_tsub_cancel_of_le h]
#align add_le_cancellable.tsub_lt_tsub_right_of_le AddLECancellable.tsub_lt_tsub_right_of_le

protected theorem tsub_lt_tsub_iff_left_of_le_of_le [ContravariantClass α α (· + ·) (· < ·)]
    (hb : AddLECancellable b) (hab : AddLECancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a) :
    a - b < a - c ↔ c < b :=
  ⟨hb.lt_of_tsub_lt_tsub_left_of_le h₂, hab.tsub_lt_tsub_left_of_le h₁⟩
#align add_le_cancellable.tsub_lt_tsub_iff_left_of_le_of_le AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le

@[simp]
protected theorem add_tsub_tsub_cancel (hac : AddLECancellable (a - c)) (h : c ≤ a) :
    a + b - (a - c) = b + c :=
  hac.tsub_eq_of_eq_add <| by rw [add_assoc, add_tsub_cancel_of_le h, add_comm]
#align add_le_cancellable.add_tsub_tsub_cancel AddLECancellable.add_tsub_tsub_cancel

protected theorem tsub_tsub_cancel_of_le (hba : AddLECancellable (b - a)) (h : a ≤ b) :
    b - (b - a) = a :=
  hba.tsub_eq_of_eq_add (add_tsub_cancel_of_le h).symm
#align add_le_cancellable.tsub_tsub_cancel_of_le AddLECancellable.tsub_tsub_cancel_of_le

protected theorem tsub_tsub_tsub_cancel_left (hab : AddLECancellable (a - b)) (h : b ≤ a) :
    a - c - (a - b) = b - c := by rw [tsub_right_comm, hab.tsub_tsub_cancel_of_le h]
#align add_le_cancellable.tsub_tsub_tsub_cancel_left AddLECancellable.tsub_tsub_tsub_cancel_left

end AddLECancellable

section Contra

/-! ### Lemmas where addition is order-reflecting. -/


variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem eq_tsub_iff_add_eq_of_le (h : c ≤ b) : a = b - c ↔ a + c = b :=
  Contravariant.AddLECancellable.eq_tsub_iff_add_eq_of_le h
#align eq_tsub_iff_add_eq_of_le eq_tsub_iff_add_eq_of_le

theorem tsub_eq_iff_eq_add_of_le (h : b ≤ a) : a - b = c ↔ a = c + b :=
  Contravariant.AddLECancellable.tsub_eq_iff_eq_add_of_le h
#align tsub_eq_iff_eq_add_of_le tsub_eq_iff_eq_add_of_le

/-- See `add_tsub_le_assoc` for an inequality. -/
theorem add_tsub_assoc_of_le (h : c ≤ b) (a : α) : a + b - c = a + (b - c) :=
  Contravariant.AddLECancellable.add_tsub_assoc_of_le h a
#align add_tsub_assoc_of_le add_tsub_assoc_of_le

theorem tsub_add_eq_add_tsub (h : b ≤ a) : a - b + c = a + c - b :=
  Contravariant.AddLECancellable.tsub_add_eq_add_tsub h
#align tsub_add_eq_add_tsub tsub_add_eq_add_tsub

theorem tsub_tsub_assoc (h₁ : b ≤ a) (h₂ : c ≤ b) : a - (b - c) = a - b + c :=
  Contravariant.AddLECancellable.tsub_tsub_assoc h₁ h₂
#align tsub_tsub_assoc tsub_tsub_assoc

theorem tsub_add_tsub_comm (hba : b ≤ a) (hdc : d ≤ c) : a - b + (c - d) = a + c - (b + d) :=
  Contravariant.AddLECancellable.tsub_add_tsub_comm Contravariant.AddLECancellable hba hdc
#align tsub_add_tsub_comm tsub_add_tsub_comm

theorem tsub_lt_iff_left (hbc : b ≤ a) : a - b < c ↔ a < b + c :=
  Contravariant.AddLECancellable.tsub_lt_iff_left hbc
#align tsub_lt_iff_left tsub_lt_iff_left

theorem tsub_lt_iff_right (hbc : b ≤ a) : a - b < c ↔ a < c + b :=
  Contravariant.AddLECancellable.tsub_lt_iff_right hbc
#align tsub_lt_iff_right tsub_lt_iff_right

theorem tsub_lt_iff_tsub_lt (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b :=
  Contravariant.AddLECancellable.tsub_lt_iff_tsub_lt Contravariant.AddLECancellable h₁ h₂
#align tsub_lt_iff_tsub_lt tsub_lt_iff_tsub_lt


@[simp]
theorem add_tsub_tsub_cancel (h : c ≤ a) : a + b - (a - c) = b + c :=
  Contravariant.AddLECancellable.add_tsub_tsub_cancel h
#align add_tsub_tsub_cancel add_tsub_tsub_cancel

/-- See `tsub_tsub_le` for an inequality. -/
theorem tsub_tsub_cancel_of_le (h : a ≤ b) : b - (b - a) = a :=
  Contravariant.AddLECancellable.tsub_tsub_cancel_of_le h
#align tsub_tsub_cancel_of_le tsub_tsub_cancel_of_le

theorem tsub_tsub_tsub_cancel_left (h : b ≤ a) : a - c - (a - b) = b - c :=
  Contravariant.AddLECancellable.tsub_tsub_tsub_cancel_left h
#align tsub_tsub_tsub_cancel_left tsub_tsub_tsub_cancel_left

end Contra

end ExistsAddOfLE

/-! ### Lemmas in a canonically ordered monoid. -/


section CanonicallyOrderedAddMonoid

variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}


@[simp]
theorem tsub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b := by
  rw [← nonpos_iff_eq_zero, tsub_le_iff_left, add_zero]
#align tsub_eq_zero_iff_le tsub_eq_zero_iff_le

alias ⟨_, tsub_eq_zero_of_le⟩ := tsub_eq_zero_iff_le
#align tsub_eq_zero_of_le tsub_eq_zero_of_le

attribute [simp] tsub_eq_zero_of_le

theorem tsub_self (a : α) : a - a = 0 :=
  tsub_eq_zero_of_le le_rfl
#align tsub_self tsub_self

theorem tsub_le_self : a - b ≤ a :=
  tsub_le_iff_left.mpr <| le_add_left le_rfl
#align tsub_le_self tsub_le_self



end CanonicallyOrderedAddMonoid
