import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Tactic.Linarith
import Lean4Repl
set_option maxHeartbeats 999999999999999999999999

/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/

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









theorem sum_Ico_Ico_comm {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i in Finset.Ico a b, ∑ j in Finset.Ico i b, f i j) =
      ∑ j in Finset.Ico a b, ∑ i in Finset.Ico a (j + 1), f i j := by lean_repl sorry
