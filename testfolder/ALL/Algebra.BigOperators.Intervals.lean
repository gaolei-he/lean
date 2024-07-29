/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Tactic.Linarith

universe u v w

open BigOperators
open Nat

namespace Finset

section Generic

variable {α : Type u} {β : Type v} {γ : Type w} {s₂ s₁ s : Finset α} {a : α} {g f : α → β}

variable [CommMonoid β]

variable {β : Type*}

variable (f g : ℕ → β) {m n : ℕ}

variable [CommGroup β]


theorem prod_Ico_add' [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → β) (a b c : α) : (∏ x in Ico a b, f (x + c)) = ∏ x in Ico (a + c) (b + c), f x := by
  rw [← map_add_right_Ico, prod_map]
  rfl

theorem prod_Ico_add [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → β) (a b c : α) : (∏ x in Ico a b, f (c + x)) = ∏ x in Ico (a + c) (b + c), f x := by
  convert prod_Ico_add' f a b c using 2
  rw [add_comm]

theorem prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
    (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b := by
  rw [Nat.Ico_succ_right_eq_insert_Ico hab]
  rw [prod_insert right_not_mem_Ico]
  rw [mul_comm]

theorem prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → β) :
    ∏ k in Ico a b, f k = f a * ∏ k in Ico (a + 1) b, f k := by
  have ha : a ∉ Ico (a + 1) b := by simp
  rw [← prod_insert ha]
  rw [Nat.Ico_insert_succ_left hab]

theorem prod_Ico_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i in Ico m n, f i) * ∏ i in Ico n k, f i) = ∏ i in Ico m k, f i :=
  Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm (prod_union (Ico_disjoint_Ico_consecutive m n k))

theorem prod_Ioc_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i in Ioc m n, f i) * ∏ i in Ioc n k, f i) = ∏ i in Ioc m k, f i := by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk, prod_union]
  apply disjoint_left.2 fun x hx h'x => _
  intros x hx h'x
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)

theorem prod_Ioc_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
    (∏ k in Ioc a (b + 1), f k) = (∏ k in Ioc a b, f k) * f (b + 1) := by
  rw [← prod_Ioc_consecutive _ hab (Nat.le_succ b), Nat.Ioc_succ_singleton, prod_singleton]

theorem prod_range_mul_prod_Ico (f : ℕ → β) {m n : ℕ} (h : m ≤ n) :
    ((∏ k in range m, f k) * ∏ k in Ico m n, f k) = ∏ k in range n, f k :=
  Nat.Ico_zero_eq_range ▸ Nat.Ico_zero_eq_range ▸ prod_Ico_consecutive f m.zero_le h

theorem prod_Ico_eq_mul_inv {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k in Ico m n, f k = (∏ k in range n, f k) * (∏ k in range m, f k)⁻¹ :=
  eq_mul_inv_iff_mul_eq.2 <| by (rw [mul_comm]; exact prod_range_mul_prod_Ico f h)

theorem prod_Ico_eq_div {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k in Ico m n, f k = (∏ k in range n, f k) / ∏ k in range m, f k := by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h

theorem prod_range_div_prod_range {α : Type*} [CommGroup α] {f : ℕ → α} {n m : ℕ} (hnm : n ≤ m) :
    ((∏ k in range m, f k) / ∏ k in range n, f k) =
    ∏ k in (range m).filter fun k => n ≤ k, f k := by
  rw [← prod_Ico_eq_div f hnm]
  congr
  apply Finset.ext
  simp only [mem_Ico, mem_filter, mem_range, *]
  tauto


theorem sum_Ico_Ico_comm {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i in Finset.Ico a b, ∑ j in Finset.Ico i b, f i j) =
      ∑ j in Finset.Ico a b, ∑ i in Finset.Ico a (j + 1), f i j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine'
    Finset.sum_bij' (fun (x : Σ _ : ℕ, ℕ) _ => (⟨x.2, x.1⟩ : Σ _ : ℕ, ℕ)) _ (fun _ _ => rfl)
      (fun (x : Σ _ : ℕ, ℕ) _ => (⟨x.2, x.1⟩ : Σ _ : ℕ, ℕ)) _ (by (rintro ⟨⟩ _; rfl))
      (by (rintro ⟨⟩ _; rfl)) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  rintro a b ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
  refine' ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;>
  linarith


theorem prod_Ico_eq_prod_range (f : ℕ → β) (m n : ℕ) :
    ∏ k in Ico m n, f k = ∏ k in range (n - m), f (m + k) := by
  by_cases h : m ≤ n
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h : n ≤ m := le_of_not_ge h
    rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty]


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
    simp only [ge_iff_le, hkm, Ico_eq_empty_of_le, prod_empty, tsub_le_iff_right, Ico_eq_empty_of_le this]



theorem prod_range_reflect (f : ℕ → β) (n : ℕ) :
    (∏ j in range n, f (n - 1 - j)) = ∏ j in range n, f j := by
  cases n
  · simp
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [prod_Ico_reflect _ _ le_rfl]
    simp


theorem prod_range_add_one_eq_factorial : ∀ n : ℕ, (∏ x in range n, (x + 1)) = n !
  | 0 => rfl
  | n + 1 => by simp [factorial, Finset.range_succ, prod_range_add_one_eq_factorial n]


theorem prod_range_succ_div_prod : ((∏ i in range (n + 1), f i) / ∏ i in range n, f i) = f n :=
  div_eq_iff_eq_mul'.mpr <| prod_range_succ f n

theorem prod_range_succ_div_top : (∏ i in range (n + 1), f i) / f n = ∏ i in range n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_range_succ f n

theorem prod_Ico_div_bot (hmn : m < n) : (∏ i in Ico m n, f i) / f m = ∏ i in Ico (m + 1) n, f i :=
  div_eq_iff_eq_mul'.mpr <| prod_eq_prod_Ico_succ_bot hmn _
