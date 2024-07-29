import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Set.Intervals.UnorderedInterval
import Mathlib.Data.Set.Intervals.Image

#align_import order.locally_finite from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

open Finset Function


class LocallyFiniteOrder (α : Type*) [Preorder α] where
  /-- Left-closed right-open interval -/
  finsetIco : α → α → Finset α
  /-- `x ∈ finsetIco a b ↔ a ≤ x ∧ x < b` -/
  finset_mem_Ico : ∀ a b x : α, x ∈ finsetIco a b ↔ a ≤ x ∧ x < b

#align locally_finite_order LocallyFiniteOrder


variable {α β : Type*}

namespace Finset

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a b x : α}

/-- The finset of elements `x` such that `a ≤ x` and `x < b`. Basically `Set.Ico a b` as a finset.
-/
def Ico (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIco a b
#align finset.Ico Finset.Ico


@[simp]
theorem mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ico a b x
#align finset.mem_Ico Finset.mem_Ico
