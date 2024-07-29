import Mathlib.Algebra.BigOperators.Multiset.Lemmas
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Pi
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Set.Pairwise.Basic

#align_import algebra.big_operators.basic from "leanprover-community/mathlib"@"fa2309577c7009ea243cffdf990cd6c84f0ad497"

/-!
# Big operators

In this file we define products and sums indexed by finite sets (specifically, `Finset`).

## Notation

We introduce the following notation, localized in `BigOperators`.
To enable the notation, use `open BigOperators`.

Let `s` be a `Finset α`, and `f : α → β` a function.

* `∏ x in s, f x` is notation for `Finset.prod s f` (assuming `β` is a `CommMonoid`)
* `∑ x in s, f x` is notation for `Finset.sum s f` (assuming `β` is an `AddCommMonoid`)
* `∏ x, f x` is notation for `Finset.prod Finset.univ f`
  (assuming `α` is a `Fintype` and `β` is a `CommMonoid`)
* `∑ x, f x` is notation for `Finset.sum Finset.univ f`
  (assuming `α` is a `Fintype` and `β` is an `AddCommMonoid`)

## Implementation Notes

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

-/


universe u v w

variable {ι : Type*} {β : Type u} {α : Type v} {γ : Type w}

open Fin

namespace Finset

/-- `∏ x in s, f x` is the product of `f x`
as `x` ranges over the elements of the finite set `s`.
-/
@[to_additive "`∑ x in s, f x` is the sum of `f x` as `x` ranges over the elements
of the finite set `s`."]
protected def prod [CommMonoid β] (s : Finset α) (f : α → β) : β :=
  (s.1.map f).prod
#align finset.prod Finset.prod
#align finset.sum Finset.sum

end Finset


namespace BigOperators

open Std.ExtendedBinder

/-- `∑ x in s, f x` is notation for `Finset.sum s f`. It is the sum of `f x`,
where `x` ranges over the finite set `s`. -/
scoped syntax (name := bigsumin) "∑ " extBinder " in " term ", " term:67 : term
scoped macro_rules (kind := bigsumin)
  | `(∑ $x:ident in $s, $r) => `(Finset.sum $s (fun $x ↦ $r))
  | `(∑ $x:ident : $t in $s, $p) => `(Finset.sum $s (fun $x:ident : $t ↦ $p))

/-- `∏ x in s, f x` is notation for `Finset.prod s f`. It is the product of `f x`,
where `x` ranges over the finite set `s`. -/
scoped syntax (name := bigprodin) "∏ " extBinder " in " term ", " term:67 : term
scoped macro_rules (kind := bigprodin)
  | `(∏ $x:ident in $s, $r) => `(Finset.prod $s (fun $x ↦ $r))
  | `(∏ $x:ident : $t in $s, $p) => `(Finset.prod $s (fun $x:ident : $t ↦ $p))


end BigOperators

open BigOperators


variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoid

variable [CommMonoid β]

@[to_additive (attr := simp)]
theorem prod_empty : ∏ x in ∅, f x = 1 :=
  rfl
#align finset.prod_empty Finset.prod_empty
#align finset.sum_empty Finset.sum_empty


@[to_additive (attr := congr)]
theorem prod_congr (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g := by
  rw [h]; exact fold_congr
#align finset.prod_congr Finset.prod_congr
#align finset.sum_congr Finset.sum_congr


@[to_additive (attr := simp)]
theorem prod_insert [DecidableEq α] : a ∉ s → ∏ x in insert a s, f x = f a * ∏ x in s, f x :=
  fold_insert
#align finset.prod_insert Finset.prod_insert
#align finset.sum_insert Finset.sum_insert

end CommMonoid

end Finset


namespace Finset

section CommMonoid

variable [CommMonoid β]


@[to_additive]
theorem prod_mul_distrib : ∏ x in s, f x * g x = (∏ x in s, f x) * ∏ x in s, g x :=
  Eq.trans (by rw [one_mul]; rfl) fold_op_distrib
#align finset.prod_mul_distrib Finset.prod_mul_distrib
#align finset.sum_add_distrib Finset.sum_add_distrib



@[to_additive]
theorem prod_range_succ_comm (f : ℕ → β) (n : ℕ) :
    (∏ x in range (n + 1), f x) = f n * ∏ x in range n, f x := by
  rw [range_succ, prod_insert not_mem_range_self]
#align finset.prod_range_succ_comm Finset.prod_range_succ_comm
#align finset.sum_range_succ_comm Finset.sum_range_succ_comm

@[to_additive]
theorem prod_range_succ (f : ℕ → β) (n : ℕ) :
    (∏ x in range (n + 1), f x) = (∏ x in range n, f x) * f n := by
  simp only [mul_comm, prod_range_succ_comm]
#align finset.prod_range_succ Finset.prod_range_succ
#align finset.sum_range_succ Finset.sum_range_succ

@[to_additive]
theorem prod_range_succ' (f : ℕ → β) :
    ∀ n : ℕ, (∏ k in range (n + 1), f k) = (∏ k in range n, f (k + 1)) * f 0
  | 0 => prod_range_succ _ _
  | n + 1 => by rw [prod_range_succ _ n, mul_right_comm, ← prod_range_succ' _ n, prod_range_succ]
#align finset.prod_range_succ' Finset.prod_range_succ'
#align finset.sum_range_succ' Finset.sum_range_succ'





-- open MulOpposite

-- section DivisionCommMonoid

-- variable [DivisionCommMonoid β]

-- @[to_additive (attr := simp)]
-- theorem prod_div_distrib : ∏ x in s, f x / g x = (∏ x in s, f x) / ∏ x in s, g x :=
--   Multiset.prod_map_div
-- #align finset.prod_div_distrib Finset.prod_div_distrib
-- #align finset.sum_sub_distrib Finset.sum_sub_distrib

-- end DivisionCommMonoid
