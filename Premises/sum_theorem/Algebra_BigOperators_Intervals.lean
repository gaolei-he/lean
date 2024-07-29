/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Tactic.Linarith

#align_import algebra.big_operators.intervals from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Results about big operators over intervals

We prove results about big operators over intervals (mostly the `ℕ`-valued `Ico m n`).
-/


universe u v w

open BigOperators
open Nat

namespace Finset

section Generic

variable {α : Type u} {β : Type v} {γ : Type w} {s₂ s₁ s : Finset α} {a : α} {g f : α → β}

variable [CommMonoid β]

@[to_additive]
theorem prod_Ico_add' [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → β) (a b c : α) : (∏ x in Ico a b, f (x + c)) = ∏ x in Ico (a + c) (b + c), f x := by
  rw [← map_add_right_Ico, prod_map]
  rfl
#align finset.prod_Ico_add' Finset.prod_Ico_add'
#align finset.sum_Ico_add' Finset.sum_Ico_add'

@[to_additive]
theorem prod_Ico_add [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → β) (a b c : α) : (∏ x in Ico a b, f (c + x)) = ∏ x in Ico (a + c) (b + c), f x := by
  convert prod_Ico_add' f a b c using 2
  rw [add_comm]
#align finset.prod_Ico_add Finset.prod_Ico_add
#align finset.sum_Ico_add Finset.sum_Ico_add

@[to_additive]
theorem prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
    (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b := by
  rw [Nat.Ico_succ_right_eq_insert_Ico hab, prod_insert right_not_mem_Ico, mul_comm]
#align finset.prod_Ico_succ_top Finset.prod_Ico_succ_top
#align finset.sum_Ico_succ_top Finset.sum_Ico_succ_top

@[to_additive]
theorem prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → β) :
    ∏ k in Ico a b, f k = f a * ∏ k in Ico (a + 1) b, f k := by
  have ha : a ∉ Ico (a + 1) b := by simp
  rw [← prod_insert ha, Nat.Ico_insert_succ_left hab]
#align finset.prod_eq_prod_Ico_succ_bot Finset.prod_eq_prod_Ico_succ_bot
#align finset.sum_eq_sum_Ico_succ_bot Finset.sum_eq_sum_Ico_succ_bot

@[to_additive]
theorem prod_Ico_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i in Ico m n, f i) * ∏ i in Ico n k, f i) = ∏ i in Ico m k, f i :=
  Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm (prod_union (Ico_disjoint_Ico_consecutive m n k))
#align finset.prod_Ico_consecutive Finset.prod_Ico_consecutive
#align finset.sum_Ico_consecutive Finset.sum_Ico_consecutive


@[to_additive]
theorem prod_range_mul_prod_Ico (f : ℕ → β) {m n : ℕ} (h : m ≤ n) :
    ((∏ k in range m, f k) * ∏ k in Ico m n, f k) = ∏ k in range n, f k :=
  Nat.Ico_zero_eq_range ▸ Nat.Ico_zero_eq_range ▸ prod_Ico_consecutive f m.zero_le h
#align finset.prod_range_mul_prod_Ico Finset.prod_range_mul_prod_Ico
#align finset.sum_range_add_sum_Ico Finset.sum_range_add_sum_Ico

@[to_additive]
theorem prod_Ico_eq_mul_inv {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k in Ico m n, f k = (∏ k in range n, f k) * (∏ k in range m, f k)⁻¹ :=
  eq_mul_inv_iff_mul_eq.2 <| by (rw [mul_comm]; exact prod_range_mul_prod_Ico f h)
#align finset.prod_Ico_eq_mul_inv Finset.prod_Ico_eq_mul_inv
#align finset.sum_Ico_eq_add_neg Finset.sum_Ico_eq_add_neg

@[to_additive]
theorem prod_Ico_eq_div {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k in Ico m n, f k = (∏ k in range n, f k) / ∏ k in range m, f k := by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h
#align finset.prod_Ico_eq_div Finset.prod_Ico_eq_div
#align finset.sum_Ico_eq_sub Finset.sum_Ico_eq_sub


@[to_additive]
theorem prod_Ico_eq_prod_range (f : ℕ → β) (m n : ℕ) :
    ∏ k in Ico m n, f k = ∏ k in range (n - m), f (m + k) := by
  by_cases h : m ≤ n
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h : n ≤ m := le_of_not_ge h
    rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty]
#align finset.prod_Ico_eq_prod_range Finset.prod_Ico_eq_prod_range
#align finset.sum_Ico_eq_sum_range Finset.sum_Ico_eq_sum_range

theorem prod_Ico_reflect (f : ℕ → β) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
    (∏ j in Ico k m, f (n - j)) = ∏ j in Ico (n + 1 - m) (n + 1 - k), f j := by
  have : ∀ i < m, i ≤ n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  cases' lt_or_le k m with hkm hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine' (prod_image _).symm
    simp only [mem_Ico]
    rintro i ⟨_, im⟩ j ⟨_, jm⟩ Hij
    rw [← tsub_tsub_cancel_of_le (this _ im), Hij, tsub_tsub_cancel_of_le (this _ jm)]
  · have : n + 1 - k ≤ n + 1 - m := by
      rw [tsub_le_tsub_iff_left h]
      exact hkm
    simp only [ge_iff_le, hkm, Ico_eq_empty_of_le, prod_empty, tsub_le_iff_right, Ico_eq_empty_of_le
      this]
#align finset.prod_Ico_reflect Finset.prod_Ico_reflect

theorem sum_Ico_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
    (h : m ≤ n + 1) : (∑ j in Ico k m, f (n - j)) = ∑ j in Ico (n + 1 - m) (n + 1 - k), f j :=
  @prod_Ico_reflect (Multiplicative δ) _ f k m n h
#align finset.sum_Ico_reflect Finset.sum_Ico_reflect

theorem prod_range_reflect (f : ℕ → β) (n : ℕ) :
    (∏ j in range n, f (n - 1 - j)) = ∏ j in range n, f j := by
  cases n
  · simp
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [prod_Ico_reflect _ _ le_rfl]
    simp
#align finset.prod_range_reflect Finset.prod_range_reflect

theorem sum_range_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (n : ℕ) :
    (∑ j in range n, f (n - 1 - j)) = ∑ j in range n, f j :=
  @prod_range_reflect (Multiplicative δ) _ f n
#align finset.sum_range_reflect Finset.sum_range_reflect


section GaussSum

/-- Gauss' summation formula -/
theorem sum_range_id_mul_two (n : ℕ) : (∑ i in range n, i) * 2 = n * (n - 1) :=
  calc
    (∑ i in range n, i) * 2 = (∑ i in range n, i) + ∑ i in range n, (n - 1 - i) :=
    by rw [sum_range_reflect (fun i => i) n, mul_two]
    _ = ∑ i in range n, (i + (n - 1 - i)) := sum_add_distrib.symm
    _ = ∑ i in range n, (n - 1) :=
      sum_congr rfl fun i hi => add_tsub_cancel_of_le <| Nat.le_pred_of_lt <| mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]
#align finset.sum_range_id_mul_two Finset.sum_range_id_mul_two

/-- Gauss' summation formula -/
theorem sum_range_id (n : ℕ) : ∑ i in range n, i = n * (n - 1) / 2 := by
  rw [← sum_range_id_mul_two n, Nat.mul_div_cancel _ zero_lt_two]
#align finset.sum_range_id Finset.sum_range_id

end GaussSum

end Generic

section Nat

variable {β : Type*}

variable (f g : ℕ → β) {m n : ℕ}

section Group

variable [CommGroup β]

@[to_additive]
theorem prod_range_succ_div_prod : ((∏ i in range (n + 1), f i) / ∏ i in range n, f i) = f n :=
  div_eq_iff_eq_mul'.mpr <| prod_range_succ f n
#align finset.prod_range_succ_div_prod Finset.prod_range_succ_div_prod
#align finset.sum_range_succ_sub_sum Finset.sum_range_succ_sub_sum

@[to_additive]
theorem prod_range_succ_div_top : (∏ i in range (n + 1), f i) / f n = ∏ i in range n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_range_succ f n
#align finset.prod_range_succ_div_top Finset.prod_range_succ_div_top
#align finset.sum_range_succ_sub_top Finset.sum_range_succ_sub_top

@[to_additive]
theorem prod_Ico_div_bot (hmn : m < n) : (∏ i in Ico m n, f i) / f m = ∏ i in Ico (m + 1) n, f i :=
  div_eq_iff_eq_mul'.mpr <| prod_eq_prod_Ico_succ_bot hmn _
#align finset.prod_Ico_div_bot Finset.prod_Ico_div_bot
#align finset.sum_Ico_sub_bot Finset.sum_Ico_sub_bot

@[to_additive]
theorem prod_Ico_succ_div_top (hmn : m ≤ n) :
    (∏ i in Ico m (n + 1), f i) / f n = ∏ i in Ico m n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_Ico_succ_top hmn _
#align finset.prod_Ico_succ_div_top Finset.prod_Ico_succ_div_top
#align finset.sum_Ico_succ_sub_top Finset.sum_Ico_succ_sub_top

end Group

end Nat
